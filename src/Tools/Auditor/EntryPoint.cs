using System;
using Bootstrap.Tools.Auditor;

namespace Microsoft.Dafny.Compilers.SelfHosting.Auditor;

public class AuditorConfiguration : Plugins.PluginConfiguration {
  internal static string[] args = new string[0];

  public override void ParseArguments(string[] args) {
    AuditorConfiguration.args = args;
  }

  public override Plugins.Rewriter[] GetRewriters(ErrorReporter errorReporter) {
    return new Plugins.Rewriter[] { new Auditor(errorReporter) };
  }

  public override Plugins.Compiler[] GetCompilers() {
    return Array.Empty<Plugins.Compiler>();
  }
}

public class Auditor : Plugins.Rewriter {

  private readonly DafnyAuditor auditor = new();

  public Auditor(ErrorReporter reporter) : base(reporter) { }

  private enum Format { HTML, Markdown, Text }

  private string GenerateHTMLReport(Program program) {
    var assembly = System.Reflection.Assembly.GetExecutingAssembly();
    var templateStream = assembly.GetManifestResourceStream("template.html");
    var templateText = new StreamReader(templateStream).ReadToEnd();
    var table = auditor.AuditHTML(program);
    return templateText.Replace("{{TABLE}}", table.ToString());
  }

  public override void PostResolve(Program program) {
    string? filename = null;
    Format format = Format.Text;
    string[] args = AuditorConfiguration.args;

    if (args.Count() > 1) {
      Console.WriteLine("DafnyAuditor takes at most one argument");
      return;
    } else if (args.Count() == 1) {
      filename = AuditorConfiguration.args[0];
      if(filename.EndsWith(".html")) {
        format = Format.HTML;
      } else if (filename.EndsWith(".md")) {
        format = Format.Markdown;
      } else if (filename.EndsWith(".txt")) {
        format = Format.Text;
      } else {
        Console.WriteLine($"Unsupported extension on report filename: {filename}");
        Console.WriteLine("Supported extensions are: .html, .md, .txt");
        return;
      }
    }

    if (filename is null) {
      auditor.AuditWarnings(Reporter, program);
    } else {
      var text = format switch {
        Format.HTML => GenerateHTMLReport(program),
        Format.Markdown => auditor.AuditMarkdown(program).ToString(),
        Format.Text => auditor.AuditText(program).ToString(),
      };

      File.WriteAllText(filename, text);
    }
  }
}

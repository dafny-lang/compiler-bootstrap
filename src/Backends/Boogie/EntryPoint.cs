using System.Collections.ObjectModel;
using Bootstrap.Backends.Boogie.Plugin;

namespace Microsoft.Dafny.Compilers.Dafny.Boogie;

internal class DafnyBoogieCompilerPlugin : Plugins.Compiler {
  private readonly DafnyBoogieCompiler compiler = new ();

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { };

  public override string TargetLanguage => "Boogie";
  public override string TargetExtension => "bpl";

  public override string PublicIdProtect(string name) {
    return name; // TODO
  }

  public override bool TextualTargetIsExecutable => true; // TODO
  public override bool SupportsInMemoryCompilation => false;

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    compiler.Compile(dafnyProgram, output);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree output) {
    compiler.EmitCallToMain(mainMethod, baseName, output);
  }

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string pathsFilename, ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter,
    out object compilationResult) {
    throw new NotImplementedException();
  }

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string pathsFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult,
    TextWriter outputWriter) {
    throw new NotImplementedException();
  }
}

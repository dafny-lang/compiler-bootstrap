using System.Collections.ObjectModel;
using Bootstrap.Backends.CSharp;

namespace Microsoft.Dafny.Compilers.Dafny.CSharp;

internal class DafnyCSharpCompilerPlugin : Plugins.Compiler {
  private readonly DafnyCSharpCompiler compiler = new ();

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".cs", ".dll" };

  public override string TargetLanguage => "C#";
  public override string TargetExtension => "cs";

  public override string PublicIdProtect(string name) {
    return new CsharpCompiler().PublicIdProtect(name);
  }

  public override bool TextualTargetIsExecutable => false;
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

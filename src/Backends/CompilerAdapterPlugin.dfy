include "../AST/Translator.Entity.dfy"

abstract module {:options "-functionSyntax:4"} Bootstrap.Backends.CompilerAdapterPlugin {
  import System
  import Microsoft.Dafny
  import AST.Entities
  import AST.Translator.Entity
  import Interop.CSharpDafnyASTModel
  import opened Interop.CSharpDafnyInterop

  trait DafnyCompiler {
    method Compile(program: Entities.Program, wr: SyntaxTreeAdapter)
    method EmitCallToMain(main: Entities.Entity, basename: string, st: SyntaxTreeAdapter)
  }

  // DISCUSS: What would be a better design here?  I'd like to have a single
  // instance of EntryPoint (not one per module refinement), and to specify the
  // constructor (not a method).
  method InitializeCompiler() returns (c: DafnyCompiler)
    ensures fresh(c)

  class {:extern} CompilerAdapter {
    var c: DafnyCompiler

    constructor() {
      var c := InitializeCompiler();
      this.c := c;
    }

    method Compile(dafnyProgram: CSharpDafnyASTModel.Program,
                   wr: Dafny.ConcreteSyntaxTree)
    {
      var st := new CSharpDafnyInterop.SyntaxTreeAdapter(wr);
      match Entity.TranslateProgram(dafnyProgram, includeCompileModules := true) {
        case Success(translated) =>
          c.Compile(translated, st);
        case Failure(err) => // FIXME return an error
          st.Write("!! Translation error: " + err.ToString());
      }
      st.Write("\n");
    }

    method EmitCallToMain(mainMethod: CSharpDafnyASTModel.Method,
                          baseName: System.String,
                          wr: Dafny.ConcreteSyntaxTree)
    {
      var st := new SyntaxTreeAdapter(wr);
      match Entity.TranslateMethod(mainMethod) {
        case Success(translated) =>
          c.EmitCallToMain(translated, TypeConv.AsString(baseName), st);
        case Failure(err) =>
          st.Write("!! Translation error: " + err.ToString());
      }
      st.Write("\n");
    }
  }
}

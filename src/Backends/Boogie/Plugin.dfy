include "../../AST/Translator.dfy"
include "../../Interop/CSharpDafnyASTModel.dfy"
include "../../Interop/CSharpDafnyInterop.dfy"
include "../../Interop/CSharpInterop.dfy"
include "../../Interop/StrTree.dfy"
include "../../Passes/EliminateNegatedBinops.dfy"
include "../../Transforms/BottomUp.dfy"
include "../../Utils/Library.dfy"
include "Compiler.dfy"

module {:options "-functionSyntax:4"} {:extern "Bootstrap.Backends.Boogie.Interface"}
  Bootstrap.Backends.Boogie.Interface
{
  import Interop.CSharpDafnyASTModel
  import opened Interop.CSharpDafnyInterop
  import opened Microsoft.Dafny
  import Utils.StrTree
  import StrTreeInterop = Interop.StrTree
  import AST.Predicates
  import AST.Translator
  import Transforms.BottomUp
  import Passes.EliminateNegatedBinops
  import opened AST.Predicates.Deep
  import Compiler

  class {:extern} DafnyBoogieCompiler {
    constructor() {
    }

    method Compile(dafnyProgram: CSharpDafnyASTModel.Program,
                   wr: ConcreteSyntaxTree) {
      var st := new StrTreeInterop.SyntaxTreeAdapter(wr);
      match Translator.TranslateProgram(dafnyProgram) {
        case Success(translated) =>
          var tree := Compiler.Compile(translated);
          st.WriteTree(tree);
        case Failure(err) => // FIXME return an error
          st.Write("!! Translation error: " + err.ToString());
      }
      st.Write("\n");
    }

    method EmitCallToMain(mainMethod: CSharpDafnyASTModel.Method,
                          baseName: System.String,
                          wr: ConcreteSyntaxTree) {
      // var st := new SyntaxTreeAdapter(wr);
      // var sClass := st.NewBlock("class __CallToMain");
      // var sBody := sClass.NewBlock("public static void Main(string[] args)");
      // sBody.WriteLine("DafnyRuntime.Helpers.WithHaltHandling(_module.Main);");
    }
  }
}

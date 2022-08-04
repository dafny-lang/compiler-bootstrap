include "../../Interop/CSharpDafnyASTModel.dfy"
include "../../Interop/CSharpInterop.dfy"
include "../../Interop/CSharpDafnyInterop.dfy"
include "../../AST/Translator.dfy"
include "../../Passes/EliminateNegatedBinops.dfy"
include "../../Transforms/BottomUp.dfy"
include "../../Utils/Library.dfy"
include "../../Utils/StrTree.dfy"
include "../../../../../../BoogieV/lang/BoogieLang.dfy"

module {:extern "Bootstrap.Backends.Boogie.Compiler"} {:options "-functionSyntax:4"}
  Bootstrap.Backends.Boogie
{
  import opened Interop.CSharpDafnyInterop
  import opened AST.Syntax
  import AST.Predicates
  import Passes.EliminateNegatedBinops
  import opened AST.Predicates.Deep
  import opened Utils.Lib.Datatypes
  import Transforms.BottomUp
  import Transforms.Generic
  import BV = BoogieLang
  import BLib = Wrappers

  type WfExpr = e: Exprs.T | Deep.All_Expr(e, Exprs.WellFormed) witness *
  const OpProgn :=
    Exprs.Eager(Exprs.Builtin(Exprs.Progn))
  const Progn: (seq<WfExpr>) --> WfExpr :=
    (es) requires |es| > 0 => var r: WfExpr := Exprs.Apply(OpProgn, es); r
}

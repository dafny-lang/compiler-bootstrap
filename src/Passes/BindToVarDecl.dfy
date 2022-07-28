include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Transforms/BottomUp.dfy"

module Bootstrap.Passes.BindToVarDecl {
  // This module desugars the binds into a scope containing a var decl.
  //
  // TODO(SMH): we don't perform any proof for now.
  //
  // Ex.:
  // ====
  // ```
  // let x := rhs in e
  //
  // ~~>
  //
  // {
  //   var x := rhs;
  //   e
  // }
  // ```

  import Utils.Lib
  import Utils.Lib.Debug
  import opened Utils.Lib.Datatypes
  import opened Transforms.BottomUp

  import opened AST.Syntax
  import opened AST.Predicates
  import opened Semantics.Interp
  import opened Semantics.Values
  import opened Semantics.Equiv
  import opened Transforms.Generic
  import opened Transforms.Proofs.BottomUp_
  import P = Predicates.Deep

  type Expr = Syntax.Expr

  function method Transform_Single(e: Expr): Expr {
    match e {
      case Bind(bvars, bvals, bbody) =>
        var vdecl := Exprs.VarDecl(bvars, Exprs.Some(bvals));
        var block := Exprs.Block([vdecl, bbody]);
        block
      case _ => e
    }
  }

  predicate Tr_Pre(p: Program) {
    true
  }

  predicate Tr_Expr_Post(e: Exprs.T) {
    true
  }

  predicate Tr_Post(p: Program)
  {
    Deep.All_Program(p, Tr_Expr_Post)
  }

  const Tr_Expr : BottomUpTransformer :=
    ( Deep.All_Expr_True_Forall(Tr_Expr_Post);
      assume IsBottomUpTransformer(Transform_Single, Tr_Expr_Post); // TODO: prove
      TR(Transform_Single, Tr_Expr_Post))

  function method Apply_Method(m: Method) : (m': Method)
    ensures Deep.All_Method(m', Tr_Expr_Post)
  {
    Deep.All_Expr_True_Forall(Tr_Expr.f.requires);
    assert Deep.All_Method(m, Tr_Expr.f.requires);
    Map_Method(m, Tr_Expr)
  }

  function method Apply(p: Program) : (p': Program)
    requires Tr_Pre(p)
    ensures Tr_Post(p')
    // Apply the transformation to a program.
  {
    Deep.All_Expr_True_Forall(Tr_Expr.f.requires);
    assert Deep.All_Program(p, Tr_Expr.f.requires);
    Map_Program(p, Tr_Expr)
  }
}

include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Transforms/BottomUp.dfy"
include "EliminateNegatedBinops.dfy"

module Bootstrap.Passes.SimplifyEmptyBlocks {
  // This module implements a simple pass, by which we simplify the empty blocks in a program.
  //
  // We do the following:
  // 1. we filter the expressions which are empty blocks in blocks of expressions (``FilterEmptyBlocks``):
  //   ```
  //   var x := f();
  //   g();
  //   {
  //     // empty block
  //   }
  //   h();
  //   ...
  //
  //      --->
  //
  //   var x := f();
  //   g();
  //   h();
  //   ...
  //   ```
  // 2. we inline the blocks which end blocks (note that we can't other blocks because of scoping
  //   issues) (``InlineLastBlock``):
  //   ```
  //   var x := f();
  //   {
  //     g();
  //     h();
  //   }
  //
  //      --->
  //
  //   var x := f();
  //   g();
  //   h();
  //   ```
  // 3. We simplify the `if then else` expressions when their branches contain empty blocks (``SimplifyIfThenElse``):
  //    ```
  //    if b then {} else {} --> {}
  //    if b then {} else e --> if !b then e else {} // This allows us to only print `if !b then e` in the output program
  //    ```
  //
  // Rk.: those transformations are complementary if performed in a bottom-up manner, as simplifying
  // some blocks might lead to the simplification of some `if then else` branches which might in
  // turn lead to the simplification of other blocks, etc.
  //
  // Rk.: one reason why we need those passes is that we transform the let binding expressions
  // coming from the Dafny ASTs to statements (more specifically, blocks containing variable
  // declarations) in the Dafny-in-Dafny AST. This leads to the introduction of unnecessary
  // blocks and hurts clarity when outputting code:
  //   ```
  //   var x := 3; // let-binding expression
  //   var y := true; // let-binding expression
  //   ...
  //
  //     --->
  //
  //   {
  //     var x := 3; // var decl statement
  //     {
  //       var y := true; // var decl statement
  //       ...
  //     }
  //   }
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

  type Expr = Syntax.Expr

  module FilterUtils {
    import opened AST.Syntax
    type Expr = Syntax.Expr

    // TODO: move?
    predicate method IsEmptyBlock(e: Expr)
    {
      e.Block? && e.stmts == []
    }

    // TODO: move?
    predicate method IsNonEmptyBlock(e: Expr)
    {
      !(IsEmptyBlock(e))
    }

  }

  module FilterEmptyBlocks {
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

    import opened FilterUtils

    type Expr = Syntax.Expr

    function method FilterEmptyBlocks_Seq(es : seq<Expr>): seq<Expr>
    {
      Seq.Filter(es, IsNonEmptyBlock)
    }

    function method FilterEmptyBlocks_Single(e: Expr): Expr
    {
      if e.Block? then
        Expr.Block(FilterEmptyBlocks_Seq(e.stmts))
      else
        e
    }

    predicate Tr_Expr_Post(e: Expr) {
      true
    }

    predicate Tr_Expr_Rel(e: Expr, e': Expr) {
      EqInterp(e, e')
    }

    lemma FilterEmptyBlocks_Seq_Rel(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
      requires forall e | e in es :: SupportsInterp(e)
      requires EqState(ctx, ctx')
      ensures EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(FilterEmptyBlocks_Seq(es), env, ctx'))
      ensures forall e | e in FilterEmptyBlocks_Seq(es) :: SupportsInterp(e)
    {
      reveal InterpBlock_Exprs();
      reveal Seq.Filter();

      var es' := FilterEmptyBlocks_Seq(es);

      var res := InterpBlock_Exprs(es, env, ctx);
      var res' := InterpBlock_Exprs(es', env, ctx');

      if es == [] {
        // Trivial
      }
      else {
        // Case disjunction: is the first expression in the sequence filtered or not?
        if IsEmptyBlock(es[0]) {
          // The first expression is filtered
          var res0 := InterpExpr(es[0], env, ctx);

          // Evaluating the first expression leaves the context unchanged
          assert res0 == Success(Return(V.Unit, ctx)) by {
            reveal InterpExpr();
            reveal InterpBlock();
            // Doesn't work without this assertion
            assert res0 == InterpBlock(es[0].stmts, env, ctx);
          }

          assert es' == FilterEmptyBlocks_Seq(es[1..]);
          FilterEmptyBlocks_Seq_Rel(es[1..], env, ctx, ctx');
        }
        else {
          // The first expression is not filtered

          // Evaluate the first expression
          var res0 := InterpExpr(es[0], env, ctx);
          var res0' := InterpExpr(es'[0], env, ctx');
          assert es[0] == es'[0];
          EqInterp_Refl_Lem(es[0]);
          EqInterp_Lem(es[0], es'[0], env, ctx, ctx');

          // Evaluate the remaining expressions
          if res0.Success? && res0.value.ret == V.Unit {
            var Return(_, ctx0) := res0.value;
            var Return(_, ctx0') := res0'.value;

            var res1 := InterpBlock_Exprs(es[1..], env, ctx0);
            var res1' := InterpBlock_Exprs(es'[1..], env, ctx0');

            assert res1 == res;
            assert res1' == res';

            FilterEmptyBlocks_Seq_Rel(es[1..], env, ctx0, ctx0');
          }
          else {
            // Trivial
          }
        }
      }
    }

    lemma FilterEmptyBlocks_Single_Rel(e: Expr)
      ensures Tr_Expr_Rel(e, FilterEmptyBlocks_Single(e))
    {
      if e.Block? && SupportsInterp(e) {
        reveal SupportsInterp();

        var e' := FilterEmptyBlocks_Single(e);
        var es := e.stmts;

        forall env, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx')) {
            FilterEmptyBlocks_Seq_Rel(es, env, ctx, ctx');
            reveal InterpExpr();
            reveal InterpBlock();
        }

        assert SupportsInterp(e');
        assert EqInterp(e, e');
      }
      else {
        EqInterp_Refl_Lem(e); 
      }
    }
  }
}

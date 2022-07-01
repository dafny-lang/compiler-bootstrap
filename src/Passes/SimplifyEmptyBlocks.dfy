include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Semantics/Pure.dfy"
include "../Transforms/BottomUp.dfy"
include "EliminateNegatedBinops.dfy"

module Bootstrap.Passes.SimplifyEmptyBlocks {
  // This module implements a simple pass, which simplifies the empty blocks in a program.
  //
  // We do the following:
  //
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
  //
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
  //
  // 3. We simplify the `if then else` expressions when their branches contain empty blocks (``SimplifyIfThenElse``):
  //    ```
  //    if b then {} else {} --> {} // if b is pure
  //    if b then {} else e --> if !b then e else {} // This allows us to only print `if !b then e` in the output program
  //    ```
  //
  // Rk.: those transformations are complementary if performed in a bottom-up manner, as simplifying
  // some blocks might lead to the simplification of some `if then else` branches which might in
  // turn lead to the simplification of other blocks, etc.
  //
  // Rk.: pass 3. removes expressions which might fail  a pass like 3. is correct, because following definition of ``EqInterp`` 
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

  module FilterCommon {
    import Utils.Lib
    import Utils.Lib.Debug

    import opened AST.Syntax
    import opened Semantics.Equiv
    import opened Semantics.Interp

    type Expr = Syntax.Expr

    const EmptyBlock := Expr.Block([])

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

    predicate Tr_Expr_Post(e: Expr) {
      true
    }

    predicate Tr_Expr_Rel(e: Expr, e': Expr) {
      EqInterp(e, e')
    }
  }

  module FilterEmptyBlocks {
    // Tranformation 1
    
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

    import opened FilterCommon

    type Expr = Syntax.Expr

    function method FilterEmptyBlocks_Seq(es: seq<Expr>): (es': seq<Expr>)
      ensures Seq_All(SupportsInterp, es) ==> Seq_All(SupportsInterp, es')
      ensures |es| >= |es'|
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

    lemma FilterEmptyBlocks_Seq_Rel(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
      requires Seq_All(SupportsInterp, es)
      requires EqState(ctx, ctx')
      ensures EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(FilterEmptyBlocks_Seq(es), env, ctx'))
    {
      reveal InterpBlock_Exprs();
      reveal Seq.Filter();

      var es' := FilterEmptyBlocks_Seq(es);

      var res := InterpBlock_Exprs(es, env, ctx);
      var res' := InterpBlock_Exprs(es', env, ctx');

      // TODO(SMH): there are too many subcases below: I'm pretty sure we can make the proofs in
      // a smarter way.
      if es == [] {
        // Trivial
      }
      else if |es| == 1 {
        assert es == [es[0]];
        reveal InterpExpr();
        reveal InterpBlock();
        if IsEmptyBlock(es[0]) {
          assert es' == [];

          // Interp(es, ctx) == ((), ctx)
          assert InterpBlock_Exprs([es[0]], env, ctx) == InterpExpr(es[0], env, ctx);
          assert InterpExpr(es[0], env, ctx) == InterpBlock_Exprs(es[0].stmts, env, ctx);
          assert InterpBlock_Exprs(es[0].stmts, env, ctx) == Success(Return(V.Unit, ctx));

          // Interp(es', ctx') == ((), ctx')
          assert InterpBlock_Exprs(es', env, ctx') == Success(Return(V.Unit, ctx'));
        }
        else {
          assert es' == es;
          EqInterp_Refl(es[0]);
          EqInterp_Inst(es[0], es[0], env, ctx, ctx');
        }
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
            assert es[0].stmts == [];
            // Doesn't work without this assertion
            assert InterpBlock(es[0].stmts, env, ctx) == InterpBlock_Exprs([], env, ctx);
          }

          assert es' == FilterEmptyBlocks_Seq(es[1..]);
          FilterEmptyBlocks_Seq_Rel(es[1..], env, ctx, ctx');
        }
        else {
          // The first expression is not filtered

          EqInterp_Refl(es[0]);
          EqInterp_Inst(es[0], es'[0], env, ctx, ctx');

          var tl := es[1..];
          var tl' := FilterEmptyBlocks_Seq(tl);

          forall env, ctx, ctx' | EqState(ctx, ctx')
            ensures EqInterpResultValue(InterpBlock_Exprs(tl, env, ctx), InterpBlock_Exprs(tl', env, ctx'))
          {
            FilterEmptyBlocks_Seq_Rel(tl, env, ctx, ctx');
          }
          InterpBlock_Exprs_Eq_Append(es[0], es[0], tl, tl', env, ctx, ctx');
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
          ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
        {
            FilterEmptyBlocks_Seq_Rel(es, env, ctx, ctx');
            reveal InterpExpr();
            reveal InterpBlock();
        }

        assert SupportsInterp(e');
        assert EqInterp(e, e');
      }
      else {
        EqInterp_Refl(e); 
      }
    }
  }

  module InlineLastBlock {
    // Tranformation 2
    
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

    import opened FilterCommon

    type Expr = Syntax.Expr

    function method InlineLastBlock_Seq(es: seq<Expr>): (es': seq<Expr>)
      ensures Seq_All(SupportsInterp, es) ==> Seq_All(SupportsInterp, es')
      // If the last expression of a sequence of expressions is a block, inline its content.
      //
      // It seems easier to reason about this function if we define it in a recursive way,
      // which is why we do so.
    {
      reveal SupportsInterp();

      // Empty sequence: nothing to do
      if es == [] then
        []
      // We reached the last statement: inline it if it is a block
      else if |es| == 1 then
        if es[0].Block? then
          assert Seq_All(SupportsInterp, es) ==> SupportsInterp(es[0]);
          assert SupportsInterp(es[0]) ==> Seq_All(SupportsInterp, es[0].stmts);
          es[0].stmts
        else
          [es[0]]
      // We haven't reached the last element: recurse on the tail
      else
        [es[0]] + InlineLastBlock_Seq(es[1..])
    }

    function method InlineLastBlock_Single(e: Expr): Expr
    {
      if e.Block? then Expr.Block(InlineLastBlock_Seq(e.stmts))
      else e
    }

    lemma InlineLastBlock_Seq_Rel(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
      requires forall e | e in es :: SupportsInterp(e)
      requires EqState(ctx, ctx')
      ensures forall e | e in InlineLastBlock_Seq(es) :: SupportsInterp(e)
      ensures EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(InlineLastBlock_Seq(es), env, ctx'))
    {
      reveal InterpBlock_Exprs();
      //reveal Seq.Filter();

      var es' := InlineLastBlock_Seq(es);

      var res := InterpBlock_Exprs(es, env, ctx);
      var res' := InterpBlock_Exprs(es', env, ctx');

      if es == [] {
        // Trivial
      }
      else if |es| == 1 {
        if es[0].Block? {
          reveal InterpExpr();
          reveal InterpBlock();

          // Doesn't work without this assertion - is it because of the fuel?
          assert res == InterpExpr(es[0], env, ctx);
          assert InterpExpr(es[0], env, ctx) == InterpBlock(es[0].stmts, env, ctx);

          assert es' == es[0].stmts;
          InterpBlock_Exprs_Refl(es[0].stmts, env, ctx, ctx');
        }
        else {
          assert es == es';
          InterpBlock_Exprs_Refl(es, env, ctx, ctx');
        }
      }
      else {
        // The first expression appears in both sequences
        EqInterp_Refl(es[0]);
        EqInterp_Inst(es[0], es'[0], env, ctx, ctx');

        // Prove that the sequence concatenations are evaluated in a similar manner
        var tl := es[1..];
        var tl' := InlineLastBlock_Seq(tl);

        forall env, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpBlock_Exprs(tl, env, ctx), InterpBlock_Exprs(tl', env, ctx'))
        {
          InlineLastBlock_Seq_Rel(tl, env, ctx, ctx');
        }
        InterpBlock_Exprs_Eq_Append(es[0], es[0], tl, tl', env, ctx, ctx');
      }
    }

    // Rk.: modulo the names, this is exactly the same proof as for ``FilterEmptyBlocks_Single_Rel``
    lemma InlineLastBlock_Single_Rel(e: Expr)
      ensures Tr_Expr_Rel(e, InlineLastBlock_Single(e))
    {
      if e.Block? && SupportsInterp(e) {
        reveal SupportsInterp();

        var e' := InlineLastBlock_Single(e);
        var es := e.stmts;

        forall env, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
        {
            InlineLastBlock_Seq_Rel(es, env, ctx, ctx');
            reveal InterpExpr();
            reveal InterpBlock();
        }

        assert SupportsInterp(e');
        assert EqInterp(e, e');
      }
      else {
        EqInterp_Refl(e); 
      }
    }
  }

  module SimplifyIfThenElse {
    // Tranformation 3
    
    import Utils.Lib
    import Utils.Lib.Debug
    import opened Utils.Lib.Datatypes
    import opened Transforms.BottomUp

    import opened AST.Syntax
    import opened AST.Predicates
    import opened Semantics.Interp
    import opened Semantics.Values
    import opened Semantics.Equiv
    import opened Semantics.Pure
    import opened Transforms.Generic
    import opened Transforms.Proofs.BottomUp_

    import opened FilterCommon

    type Expr = Syntax.Expr

    function method SimplifyEmptyIfThenElse_Single(e: Expr): Expr
      // Tranformation 3.1: `if b then {} else {} ---> {}`
      //
      // Eliminating `b` might lead to a program which fails less. We might want to be
      // more precise in case we deal with potentially non-terminating programs, for instance
      // by checking that `b` doesn't call any (potentially non-terminating) method.
    {
      // We might want to check that `e.cond` terminates
      if e.If? && IsPure(e.cond) && IsEmptyBlock(e.thn) && IsEmptyBlock(e.els) then EmptyBlock
      else e
    }

    lemma SimplifyEmptyIfThenElse_Single_Rel(e: Expr)
      ensures Tr_Expr_Rel(e, SimplifyEmptyIfThenElse_Single(e))
    {
      if e.If? && IsPure(e.cond) && IsEmptyBlock(e.thn) && IsEmptyBlock(e.els) && SupportsInterp(e) {
        var e' := SimplifyEmptyIfThenElse_Single(e);
        reveal SupportsInterp();

        forall env, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
        {
          var res := InterpExpr(e, env, ctx);
          var res0 := InterpExprWithType(e.cond, Type.Bool, env, ctx);

          if res0.Success? {
            var Return(b, ctx0) := res0.value;

            InterpExprWithType_IsPure_SameState(e.cond, Type.Bool, env, ctx);
            assert ctx0 == ctx;
            
            assert res == InterpExpr(EmptyBlock, env, ctx0) by {
              reveal InterpExpr();
            }

            EqInterp_Refl(EmptyBlock);
            EqInterp_Inst(EmptyBlock, EmptyBlock, env, ctx, ctx');
          }
          else {
            assert res.Failure? by {
              reveal InterpExpr();
            }
          }
        }

        assert SupportsInterp(e');
      }
      else {
        EqInterp_Refl(e);
      }
    }
  }
}

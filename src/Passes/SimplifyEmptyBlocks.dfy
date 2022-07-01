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
  // This module implements a simple pass, which simplifies the empty blocks in a program.
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

  type {:verify false} Expr = Syntax.Expr

  module FilterCommon {
    import Utils.Lib
    import Utils.Lib.Debug

    import opened AST.Syntax
    import opened Semantics.Equiv
    import opened Semantics.Interp
    import opened Transforms.BottomUp // For the def of ``TODO()``

    type {:verify false} Expr = Syntax.Expr

    // TODO: move?
    predicate method {:verify false} IsEmptyBlock(e: Expr)
    {
      e.Block? && e.stmts == []
    }

    // TODO: move?
    predicate method {:verify false} IsNonEmptyBlock(e: Expr)
    {
      !(IsEmptyBlock(e))
    }

    // TODO: move
    predicate Seq_All<T>(f: T -> bool, s: seq<T>)
    {
      forall x | x in s :: f(x)
    }

    predicate {:verify false} Tr_Expr_Post(e: Expr) {
      true
    }

    predicate {:verify false} Tr_Expr_Rel(e: Expr, e': Expr) {
      EqInterp(e, e')
    }


    // TODO: move
    predicate {:verify false} EqInterpBlockExprs(es: seq<Exprs.T>, es': seq<Exprs.T>)
    {
      Seq_All(SupportsInterp, es) ==>
      (&& Seq_All(SupportsInterp, es')
       && forall env, ctx, ctx' | EqState(ctx, ctx') ::
         EqInterpResultValue(
                        InterpBlock_Exprs(es, env, ctx),
                        InterpBlock_Exprs(es', env, ctx')))
    }

    // TODO: move
    lemma {:verify false} EqInterpBlockExprs_Inst(es: seq<Exprs.T>, es': seq<Exprs.T>, env: Environment, ctx: State, ctx': State)
      requires EqInterpBlockExprs(es, es')
      requires Seq_All(SupportsInterp, es)
      requires EqState(ctx, ctx')
      ensures  EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es', env, ctx'))
    {}
    
    // TODO: move
    lemma {:verify false} InterpBlock_Exprs_Eq_Append(e: Expr, e': Expr, tl: seq<Expr>, tl': seq<Expr>, env: Environment, ctx: State, ctx': State)
      requires SupportsInterp(e)
      requires SupportsInterp(e')
      requires Seq_All(SupportsInterp, tl)
      requires Seq_All(SupportsInterp, tl')
      requires EqState(ctx, ctx')
      requires EqInterp(e, e')
      requires EqInterpBlockExprs(tl, tl')
      requires |tl| > 0
      ensures EqInterpResultValue(InterpBlock_Exprs([e] + tl, env, ctx), InterpBlock_Exprs([e'] + tl', env, ctx'))
      // Auxiliary lemma for the proofs about transformations operating on blocks. This is especially
      // useful when those transformations might update the length of the sequence of expressions
      // in the blocks. The proof is a bit tricky, because the case where the sequence has length 1
      // is a special case in the definition of ``EqInterpBlock_Exprs``.
    {
      var es := [e] + tl;
      var es' := [e'] + tl';
      assert e == es[0];

      reveal InterpBlock_Exprs();

      // Evaluate the first expression
      var res0 := InterpExpr(e, env, ctx);
      var res0' := InterpExpr(e', env, ctx');
      EqInterp_Lem(e, e', env, ctx, ctx');

      // We need to make a case disjunction on whether the length of the concatenated sequences is
      // > 1 or not
      if |tl'| >= 1 {
        // The "regular" case

        // Evaluate the remaining expressions
        if res0.Success? && res0.value.ret == V.Unit {
          var Return(_, ctx0) := res0.value;
          var Return(_, ctx0') := res0'.value;

          var res1 := InterpBlock_Exprs(tl, env, ctx0);
          var res1' := InterpBlock_Exprs(tl', env, ctx0');

          EqInterpBlockExprs_Inst(tl, tl', env, ctx0, ctx0');
        }
        else {
          // Trivial
        }
      }
      else {
        // Degenerate case
        assert |tl'| == 0;

        if res0.Success? {
          var Return(v, ctx0) := res0.value;
          var Return(v', ctx0') := res0'.value;

          if v == V.Unit {
            assert v' == V.Unit;
            EqInterpBlockExprs_Inst(tl, tl', env, ctx0, ctx0');
          }
          else {
            assert v' != V.Unit;

            // TODO(SMH): update EqInterp so that this works (evaluating `es` will fail if `e` doesn't
            // evaluate to `Unit`)
            assume TODO();
          }
        }
        else {
          // Trivial
        }
      }
    }

    // TODO: move
    predicate EqInterpResultValue_Strong(res: InterpResult<WV>, res': InterpResult<WV>) {
      match (res, res') {
        case (Success(Return(v,ctx)), Success(Return(v',ctx'))) =>
          && v == v'
          && ctx == ctx'
        case (Failure(err), Failure(err')) =>
          err == err'
        case _ =>
          false
      }
    }

    // TODO: move
    // TODO: remove? This lemma is trivial.
    lemma {:verify false} InterpBlock_Exprs1_Strong_Eq(e: Expr, env: Environment, ctx: State)
      requires SupportsInterp(e)
      ensures EqInterpResultValue_Strong(InterpExpr(e, env, ctx), InterpBlock_Exprs([e], env, ctx))
      // Auxiliary lemma: evaluating a block of one expression is equivalent to evaluating
      // the single expression.
    {
      reveal InterpBlock_Exprs();
    }

    // TODO: move
    lemma {:verify false} InterpBlock_Exprs_Refl(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
      requires Seq_All(SupportsInterp, es)
      requires EqState(ctx, ctx')
      ensures EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es, env, ctx'))
    {
      reveal InterpBlock_Exprs();
      if es == [] {}
      else {
         // Evaluate the first expression
        var res0 := InterpExpr(es[0], env, ctx);
        var res0' := InterpExpr(es[0], env, ctx');
        EqInterp_Refl_Lem(es[0]);
        EqInterp_Lem(es[0], es[0], env, ctx, ctx');

        // Evaluate the remaining expressions
        if res0.Success? && res0.value.ret == V.Unit {
          var Return(_, ctx0) := res0.value;
          var Return(_, ctx0') := res0'.value;

          InterpBlock_Exprs_Refl(es[1..], env, ctx0, ctx0');
        }
        else {
          // Trivial
        }
      }
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

    type {:verify false} Expr = Syntax.Expr

    function method {:verify false} FilterEmptyBlocks_Seq(es: seq<Expr>): (es': seq<Expr>)
      ensures Seq_All(SupportsInterp, es) ==> Seq_All(SupportsInterp, es')
      ensures |es| >= |es'|
    {
      Seq.Filter(es, IsNonEmptyBlock)
    }

    function method {:verify false} FilterEmptyBlocks_Single(e: Expr): Expr
    {
      if e.Block? then
        Expr.Block(FilterEmptyBlocks_Seq(e.stmts))
      else
        e
    }

    lemma {:verify false} FilterEmptyBlocks_Seq_Rel(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
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
          EqInterp_Refl_Lem(es[0]);
          EqInterp_Lem(es[0], es[0], env, ctx, ctx');
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
          }

          assert es' == FilterEmptyBlocks_Seq(es[1..]);
          FilterEmptyBlocks_Seq_Rel(es[1..], env, ctx, ctx');
        }
        else {
          // The first expression is not filtered

          EqInterp_Refl_Lem(es[0]);
          EqInterp_Lem(es[0], es'[0], env, ctx, ctx');

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

    lemma {:verify false} FilterEmptyBlocks_Single_Rel(e: Expr)
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
        EqInterp_Refl_Lem(e); 
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

    type {:verify false} Expr = Syntax.Expr

    function method {:verify false} InlineLastBlock_Seq(es: seq<Expr>): (es': seq<Expr>)
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

    function method {:verify false} InlineLastBlock_Single(e: Expr): Expr
    {
      if e.Block? then Expr.Block(InlineLastBlock_Seq(e.stmts))
      else e
    }

    lemma {:verify false} InlineLastBlock_Seq_Rel(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
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
        EqInterp_Refl_Lem(es[0]);
        EqInterp_Lem(es[0], es'[0], env, ctx, ctx');

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
    lemma {:verify true} InlineLastBlock_Single_Rel(e: Expr)
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
        EqInterp_Refl_Lem(e); 
      }
    }
  }
}

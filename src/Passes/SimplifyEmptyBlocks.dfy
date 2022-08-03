include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Semantics/Pure.dfy"
include "../Semantics/EqInterpRefl.dfy"
include "../Semantics/EqInterpScopes.dfy"
include "../Semantics/InterpStateIneq.dfy"
include "../Transforms/BottomUp.dfy"
include "EliminateNegatedBinops.dfy"

module Bootstrap.Passes.SimplifyEmptyBlocks {
  // This module implements a pass that simplifies empty blocks in a program.
  //
  // We do the following:
  //
  // 1. we filter empty blocks in blocks of expressions (``FilterEmptyBlocks``):
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
  // 2. we inline the blocks that end blocks (note that we can't inline other blocks because of scoping
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
  // 3. We simplify `if then else` expressions when their branches contain empty blocks (``SimplifyIfThenElse``):
  //    ```
  //    if b then {} else {} --> {} // if b is pure
  //    if b then {} else e --> if !b then e else {} // This allows us to only print `if !b then e` in the output program
  //    ```
  //
  // Rk.: those transformations are complementary if performed in a bottom-up manner, as simplifying
  // some blocks might lead to the simplification of some `if then else` branches which might in
  // turn lead to the simplification of other blocks, etc.
  //
  // Rk.: pass 3. removes expressions that might fail. A pass like (3.) is correct because, following definition of ``EqInterp``, the original program (before simplification) is assumed to not fail. 
  //
  // Rk.: one reason why we need these passes is that Dafny-in-Dafny unifies let
  // expressions and variable-declaration statements. For let expressions, this
  // can lead to the introduction of unnecessary blocks and hurt readability.
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
  //
  // Another reason is that a lot of empty blocks are introduced by ghost code.

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
  import opened Utils.Lib.Datatypes

  import opened AST.Syntax
  import opened Semantics.Equiv
  import opened Semantics.Interp

  type Expr = Syntax.Expr
  type Context = Interp.Context

  // TODO: move?
  predicate method IsEmptyBlock(e: Expr)
  {
    e.Block? && e.stmts == []
  }

  lemma IsEmptyBlock_Eq(e: Expr)
    ensures IsEmptyBlock(e) <==> e == EmptyBlock
    // For sanity
  {}

  // TODO: move?
  predicate method IsNotEmptyBlock(e: Expr)
  {
    !IsEmptyBlock(e)
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
  import EqRefl = Semantics.EqInterpRefl
  import EqScopes = Semantics.EqInterpScopes
  import opened Semantics.InterpStateIneq
  import opened Transforms.Generic
  import opened Transforms.Proofs.BottomUp_

  import opened FilterCommon

  type Expr = Syntax.Expr
  type Context = FilterCommon.Context

  function method FilterEmptyBlocks_Seq(es: seq<Expr>): (es': seq<Expr>)
    ensures Seq_All(SupportsInterp, es) ==> Seq_All(SupportsInterp, es')
    ensures |es| >= |es'|
  {
    Seq.Filter(es, IsNotEmptyBlock)
  }

  function method FilterEmptyBlocks_Single(e: Expr): Expr
  {
    if e.Block? then
      Expr.Block(FilterEmptyBlocks_Seq(e.stmts))
    else
      e
  }

  lemma FilterEmptyBlocks_Seq_Rel(es: seq<Expr>, env: Environment, keys:set<string>, ctx: State, ctx': State)
    requires Seq_All(SupportsInterp, es)
    requires EqState(ctx, ctx')
    requires EqScopes.StateHasKeys(ctx, keys)
    requires EqScopes.StateHasKeys(ctx', keys)
    ensures EqScopes.EqResultRolledValue(keys, InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(FilterEmptyBlocks_Seq(es), env, ctx'))
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
      reveal GEqCtx(); // TODO: remove?
      reveal EqScopes.Base.EqSubCtx();
    }
    else if |es| == 1 {
      assert es == [es[0]];
      reveal InterpExpr();
      reveal InterpBlock();
      if IsEmptyBlock(es[0]) {
        assert es' == [];

        // Interp(es, ctx) == ((), ctx)
        assert InterpBlock_Exprs([es[0]], env, ctx) == Success(Return(V.Unit, ctx)) by {
          assert InterpBlock_Exprs([es[0]], env, ctx) == InterpExpr(es[0], env, ctx);
          Interp_EmptyBlock(env, ctx);
        }

        // Interp(es', ctx') == ((), ctx')
        assert InterpBlock_Exprs(es', env, ctx') == Success(Return(V.Unit, ctx')) by {
          Interp_EmptyBlock(env, ctx');
        }

        reveal GEqCtx();
        reveal EqScopes.Base.EqSubCtx();
      }
      else {
        assert es' == es;
        EqRefl.InterpExpr_EqRefl(es[0], env, ctx, ctx');
        InterpExpr_StateSmaller(es[0], env, ctx);
        InterpExpr_StateSmaller(es[0], env, ctx');
        reveal GEqCtx();
        reveal EqScopes.Base.EqSubCtx();
      }
    }
    else {
      // Case disjunction: is the first expression in the sequence filtered or not?
      if IsEmptyBlock(es[0]) {

        // The first expression is filtered
        var res0 := InterpExpr(es[0], env, ctx);

        // Evaluating the first expression leaves the context unchanged
        assert res0 == Success(Return(V.Unit, ctx)) by {
          Interp_EmptyBlock(env, ctx);
        }

        // Doesn't work without this assertion
        assert res0 == InterpExprWithType(es[0], Types.Unit, env, ctx);

        assert es' == FilterEmptyBlocks_Seq(es[1..]);
        FilterEmptyBlocks_Seq_Rel(es[1..], env, keys, ctx, ctx');
      }
      else {
        // The first expression is not filtered
        EqRefl.InterpExpr_EqRefl(es[0], env, ctx, ctx');

        var tl := es[1..];
        var tl' := FilterEmptyBlocks_Seq(tl);

        assert EqScopes.EqInterpBlockExprs(tl, tl', keys) by {
          forall env, ctx, ctx' | EqState(ctx, ctx') && EqScopes.StateHasKeys(ctx, keys) && EqScopes.StateHasKeys(ctx', keys)
            ensures EqScopes.EqInterpBlockExprs_Single(tl, tl', env, keys, ctx, ctx')
          {
            FilterEmptyBlocks_Seq_Rel(tl, env, keys, ctx, ctx');
          }
          reveal EqScopes.EqInterpBlockExprs();
        }
        EqScopes.InterpBlock_Exprs_Eq_Append(es[0], tl, tl', env, keys, ctx, ctx');
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
          reveal InterpExpr();
          reveal InterpBlock();

          var ctx1 := StartScope(ctx);
          var ctx1' := StartScope(ctx');

          assert EqState(ctx1, ctx1') by {
            reveal GEqCtx();
          }

          var keys := ctx.locals.Keys;
          assert keys == ctx'.locals.Keys by { reveal GEqCtx(); }
          
          FilterEmptyBlocks_Seq_Rel(es, env, keys, ctx1, ctx1');
          var res2 := InterpBlock_Exprs(es, env, ctx1);
          var res2' := InterpBlock_Exprs(FilterEmptyBlocks_Seq(es), env, ctx1');
          assert EqScopes.EqResultRolledValue(keys, res2, res2') by { reveal GEqCtx(); }

          if res2.Success? {
            var Return(v, ctx2) := res2.value;
            var Return(v', ctx2') := res2'.value;
            assert EqValue(v, v');
            assert EqScopes.EqStateRolled(keys, ctx2, ctx2');

            var ctx3 := EndScope(ctx, ctx2);
            var ctx3' := EndScope(ctx', ctx2');
            assert EqState(ctx3, ctx3') by { reveal GEqCtx(); reveal EqScopes.Base.EqSubCtx(); }
            reveal GEqCtx();
          }
          else {}
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
  //
  // Rk.: the key element in the correctness proof is the invariant provided by the
  // lemmas in the ``EqInterpScopes`` module.
  
  import Utils.Lib
  import Utils.Lib.Debug
  import opened Utils.Lib.Datatypes
  import opened Transforms.BottomUp

  import opened AST.Syntax
  import opened AST.Predicates
  import opened Semantics.Interp
  import opened Semantics.Values
  import opened Semantics.Equiv
  import opened Semantics.EqInterpRefl
  import EqRefl = Semantics.EqInterpRefl
  import EqScopes = Semantics.EqInterpScopes
  import opened Semantics.InterpStateIneq
  import opened Transforms.Generic
  import opened Transforms.Proofs.BottomUp_

  import opened FilterCommon

  type Expr = Syntax.Expr
  type Context = Interp.Context
  type Value = Interp.Value

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

  lemma InlineLastBlock_Seq_Rel(es: seq<Expr>, env: Environment, keys: set<string>, ctx: State, ctx': State)
    requires forall e | e in es :: SupportsInterp(e)
    requires EqState(ctx, ctx')
    requires EqScopes.StateHasKeys(ctx, keys)
    requires EqScopes.StateHasKeys(ctx', keys)
    ensures forall e | e in InlineLastBlock_Seq(es) :: SupportsInterp(e)
    ensures EqScopes.EqResultRolledValue(keys, InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(InlineLastBlock_Seq(es), env, ctx'))
  {
    reveal InterpBlock_Exprs();

    var es' := InlineLastBlock_Seq(es);

    var res := InterpBlock_Exprs(es, env, ctx);
    var res' := InterpBlock_Exprs(es', env, ctx');

    if es == [] {
      // Trivial
      assert EqScopes.EqResultRolledValue(keys, res, res') by { reveal GEqCtx(); reveal EqScopes.Base.EqSubCtx(); }
    }
    else if |es| == 1 {
      if es[0].Block? {
        reveal InterpExpr();
        reveal InterpBlock();

        // Doesn't work without this assertion - is it because of the fuel?
        assert res == InterpExpr(es[0], env, ctx);
        assert InterpExpr(es[0], env, ctx) == InterpBlock(es[0].stmts, env, ctx);

        var ctx1 := StartScope(ctx);
        assert es' == es[0].stmts;

        var or := ctx.rollback;
        var or' := map [];
        var ctx_start := ctx1;
        var ctx_start' := ctx';
        assert EqCtx(ctx_start.rollback + or, ctx_start'.rollback + or') by { reveal GEqCtx(); }
        EqScopes.InterpExprs_Eq(es', env, or, ctx_start, or', ctx_start');

        assert InterpExpr(es[0], env, ctx) == InterpBlock(es', env, ctx) by { reveal InterpExpr(); }

        InterpExprs_Block_Equiv_Strong(es', env, ctx_start);
        InterpExprs_Block_Equiv_Strong(es', env, ctx_start');

        if res.Success? {
          reveal InterpBlock();
          reveal InterpExprs_Block();

          var Return(v, ctx2) := InterpBlock_Exprs(es', env, ctx_start).value;
          var ctx3 := EndScope(ctx, ctx2);
          assert res == Success(Return(v, ctx3));

          var Return(v', ctx3') := InterpBlock_Exprs(es', env, ctx_start').value;
          assert res' == Success(Return(v', ctx3'));

          // The following assertions are given by ``EqScopes.InterpExprs_Eq``
          assert EqCtx(ctx2.locals, ctx3'.locals);
          assert EqScopes.EqOuterRollback(or, ctx2, or', ctx3');
          assert EqCtx(ctx2.rollback + or, ctx3'.rollback + or');

          assert ctx'.locals.Keys + ctx'.rollback.Keys <= ctx3'.locals.Keys + ctx3'.rollback.Keys by {
            InterpBlock_Exprs_StateSmaller(es', env, ctx_start');
          }

          assert ctx.locals.Keys <= ctx2.locals.Keys + ctx2.rollback.Keys by {
            InterpBlock_Exprs_StateSmaller(es', env, ctx_start);
          }

          assert EqScopes.Base.EqRolled(keys, ctx3, ctx3') by {
            assert ctx3.locals == map x | x in ctx.locals.Keys :: (ctx2.locals + ctx2.rollback)[x];
            assert ctx3.rollback == ctx.rollback;

            var rolled := (ctx3.locals + ctx3.rollback);
            var rolled' := (ctx3'.locals + ctx3'.rollback);
            assert keys <= rolled.Keys;
            assert keys <= rolled'.Keys;
            assert forall x | x in keys :: EqValue(rolled[x], rolled'[x]) by {
              reveal GEqCtx();
            }

            reveal EqScopes.Base.EqSubCtx();
          }

          assert EqScopes.EqResultRolledValue(keys, res, res');
        }
        else {}
      }
      else {
        assert es == es';
        assert Seq_All(SupportsInterp, es);
        EqRefl.InterpBlock_Exprs_EqRefl(es, env, ctx, ctx');
        InterpBlock_Exprs_StateSmaller(es, env, ctx);
        InterpBlock_Exprs_StateSmaller(es, env, ctx');
        assert EqInterpResultValue(res, res');
        assert EqScopes.EqResultRolledValue(keys, res, res') by { reveal GEqCtx(); reveal EqScopes.Base.EqSubCtx(); }
      }
    }
    else {
      // Prove that the sequence concatenations are evaluated in a similar manner
      var tl := es[1..];
      var tl' := InlineLastBlock_Seq(tl);

      assert EqScopes.EqInterpBlockExprs(tl, tl', keys) by {
        forall env, ctx, ctx' | EqState(ctx, ctx') && EqScopes.StateHasKeys(ctx, keys) && EqScopes.StateHasKeys(ctx', keys)
          ensures EqScopes.EqInterpBlockExprs_Single(tl, tl', env, keys, ctx, ctx')
        {
          InlineLastBlock_Seq_Rel(tl, env, keys, ctx, ctx');
        }
        reveal EqScopes.EqInterpBlockExprs();
      }
      EqScopes.InterpBlock_Exprs_Eq_Append(es[0], tl, tl', env, keys, ctx, ctx');
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
      var es' := e'.stmts;

      forall env, ctx, ctx' | EqState(ctx, ctx')
        ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
      {
        reveal InterpExpr();
        reveal InterpBlock();

        assert ctx.locals.Keys == ctx'.locals.Keys by { reveal GEqCtx(); }
        var keys := ctx.locals.Keys;

        var ctx1 := StartScope(ctx);
        var ctx1' := StartScope(ctx');

        assert EqState(ctx1, ctx1') by {
          reveal GEqCtx();
        }

        InlineLastBlock_Seq_Rel(es, env, keys, ctx1, ctx1');
        reveal GEqCtx();
        reveal EqScopes.Base.EqSubCtx();
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

  // TODO(SMH): factorize with ``EliminateNegatedBinops``?
  function method NegateExpr(e: Expr): (e':Expr)
    ensures SupportsInterp(e) ==> SupportsInterp(e')
  {
    reveal SupportsInterp();
    Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [e])
  }

  // TODO(SMH): factorize with ``EliminateNegatedBinops``?
  lemma InterpExpr_NegateExpr(e: Expr, env: Environment, ctx: State)
    requires SupportsInterp(e)
    ensures
      match InterpExpr(e, env, ctx)
        case Failure(_) => true
        case Success(Return(v, ctx1)) =>
          match InterpExpr(NegateExpr(e), env, ctx)
          case Failure(_) => !v.Bool?
          case Success(Return(v', ctx1')) =>
            && v.Bool?
            && v'.Bool?
            && v.b == !v'.b
            && ctx1' == ctx1
  {
    var res := InterpExpr(e, env, ctx);
    var e' := NegateExpr(e);
    var res' := InterpExpr(e', env, ctx);

    var args := [e];
    var args_res := InterpExprs(args, env, ctx);
    InterpExprs1_Strong_Eq(e, env, ctx);

    reveal InterpExpr();
    
    if args_res.Success? {
      reveal InterpUnaryOp();
    }
    else {}
  }

  function method NegateIfThenElse_Single(e: Expr): (e': Expr)
    ensures SupportsInterp(e) ==> SupportsInterp(e')
    // Auxiliary transformation: `if b then e0 else e1 ---> if !b then e1 else e0`
  {
    reveal SupportsInterp();
    if e.If? then Expr.If(NegateExpr(e.cond), e.els, e.thn)
    else e
  }
  
  
  lemma NegateIfThenElse_Single_Rel(e: Expr)
    ensures Tr_Expr_Rel(e, NegateIfThenElse_Single(e))
  {
    if e.If? && SupportsInterp(e) {
      var e' := NegateIfThenElse_Single(e);
      
      reveal SupportsInterp();

      forall env, ctx, ctx' | EqState(ctx, ctx')
        ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
      {
        var res := InterpExpr(e, env, ctx);
        var res' := InterpExpr(e', env, ctx);

        var res0 := InterpExprWithType(e.cond, Type.Bool, env, ctx);
        var res0' := InterpExprWithType(e.cond, Type.Bool, env, ctx');

        EqInterp_Refl(e.cond);
        EqInterp_Inst(e.cond, e.cond, env, ctx, ctx');
        
        var res0'' := InterpExprWithType(e'.cond, Type.Bool, env, ctx');
        InterpExpr_NegateExpr(e.cond, env, ctx');

        reveal InterpExpr();
        if res.Success? {
          assert res0'.Success?;
          assert res0''.Success?;

          var Return(b, ctx0) := res0.value;
          var Return(b'', ctx0'') := res0''.value;

          assert b.Bool? && b''.Bool? && b.b == !b''.b;

          EqInterp_Refl(e.thn);
          EqInterp_Inst(e.thn, e.thn, env, ctx0, ctx0'');
          EqInterp_Refl(e.els);
          EqInterp_Inst(e.els, e.els, env, ctx0, ctx0'');
        }
        else {}
      }

      assert SupportsInterp(e');
    }
    else {
      EqInterp_Refl(e);
    }
  }

  function method NegateIfThenElseIfEmptyThen_Single(e: Expr): (e': Expr)
    ensures SupportsInterp(e) ==> SupportsInterp(e')
    // Tranformation 3.2: `if b then {} else e ---> if !b then e else {}`
  {
    reveal SupportsInterp();
    if e.If? && IsEmptyBlock(e.thn) then NegateIfThenElse_Single(e)
    else e
  }

  lemma NegateIfThenElseIfEmptyThen_Single_Rel(e: Expr)
    ensures Tr_Expr_Rel(e, NegateIfThenElseIfEmptyThen_Single(e))
  {
    if e.If? && IsEmptyBlock(e.thn) {
      NegateIfThenElse_Single_Rel(e);
    }
    else {
      EqInterp_Refl(e);
    }
  }

  function method Simplify_Single(e: Expr): (e': Expr)
    ensures SupportsInterp(e) ==> SupportsInterp(e')
    ensures Tr_Expr_Rel(e, e')
    // The full transformation 3
  {
    reveal SupportsInterp();
    var e1 := SimplifyEmptyIfThenElse_Single(e);
    SimplifyEmptyIfThenElse_Single_Rel(e);
    var e2 := NegateIfThenElseIfEmptyThen_Single(e1);
    NegateIfThenElseIfEmptyThen_Single_Rel(e1);
    EqInterp_Trans(e, e1, e2);
    e2
  } 
}

module Simplify {
  /// The final transformation
  
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
  import FilterEmptyBlocks
  import InlineLastBlock
  import SimplifyIfThenElse

  type Expr = Syntax.Expr

  function method Simplify_Single(e: Expr): (e': Expr)
    ensures SupportsInterp(e) ==> SupportsInterp(e')
    ensures EqInterp(e, e')
    // This function puts all the transformation together
  {
    var e1 := FilterEmptyBlocks.FilterEmptyBlocks_Single(e);
    FilterEmptyBlocks.FilterEmptyBlocks_Single_Rel(e);
    assert EqInterp(e, e1);
    var e2 := InlineLastBlock.InlineLastBlock_Single(e1);
    InlineLastBlock.InlineLastBlock_Single_Rel(e1);
    assert EqInterp(e1, e2);
    var e3 := SimplifyIfThenElse.Simplify_Single(e2);
    assert EqInterp(e2, e3);

    EqInterp_Trans(e, e1, e2);
    EqInterp_Trans(e, e2, e3);
    assert EqInterp(e, e3);

    e3
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
      assert IsBottomUpTransformer(Simplify_Single, Tr_Expr_Post);
      TR(Simplify_Single,
         Tr_Expr_Post))

  function method Apply_Method(m: Method) : (m': Method)
    ensures Deep.All_Method(m', Tr_Expr_Post)
    ensures Tr_Expr_Rel(m.methodBody, m'.methodBody)
    // Apply the transformation to a method.
    //
    // We need it on a temporary basis, so that we can apply the transformation
    // to all the methods in a program (we haven't defined modules, classes,
    // etc. yet). When the `Program` definition is complete enough, we will
    // remove this definition and exclusively use `Apply`.
  {
    Deep.All_Expr_True_Forall(Tr_Expr.f.requires);
    assert Deep.All_Method(m, Tr_Expr.f.requires);
    EqInterp_Lift(Tr_Expr.f);
    Map_Method_PreservesRel(m, Tr_Expr, Tr_Expr_Rel);
    Map_Method(m, Tr_Expr)
  }

  function method Apply(p: Program) : (p': Program)
    requires Tr_Pre(p)
    ensures Tr_Post(p')
    ensures Tr_Expr_Rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
    // Apply the transformation to a program.
  {
    Deep.All_Expr_True_Forall(Tr_Expr.f.requires);
    assert Deep.All_Program(p, Tr_Expr.f.requires);
    EqInterp_Lift(Tr_Expr.f);
    Map_Program_PreservesRel(p, Tr_Expr, Tr_Expr_Rel);
    Map_Program(p, Tr_Expr)
  }
}

}


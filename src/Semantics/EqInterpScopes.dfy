include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "Interp.dfy"
include "Equiv.dfy"
include "ExprInduction.dfy"
include "InterpStateIneq.dfy"

module Bootstrap.Semantics.EqInterpScopes.Base refines ExprInduction {
  // This module provides lemmas which state that evaluating an expression with equivalent contexts
  // leads to equivalent results. The meaning of "equivalent contexts" here is given by ``EqResult``
  // below. We need this quite general notion to prove, for instance, that it is ok to flatten a
  // block ending another block, or in other words that transformations like the following one preserve
  // the semantics of the program:
  // ```
  // {
  //   var x := 0;
  //   f(x);
  //   {
  //     x := 1;
  //     g(x);
  //     var x := true;
  //     var y := 2;
  //     h(x, y);
  //   }
  //   // (i)
  // }
  // 
  //     ~~>
  //
  // {
  //   var x := 0;
  //   f(x);
  //   x := 1;
  //   g(x);
  //   var x := true;
  //   var y := 2;
  //   h(x, y);
  //   // (i)
  // }
  // ```
  //
  // An important point in the transformation above is that when reaching (i), the environments
  // in the two programs is not the same: for instance, in the transformed program we have a
  // binding `y -> 2`, which is not present in the environment of the original program (because
  // it went out of scope). However, if we pop one more scope we do get equivalent environments.
  // Building on this insight, we prove an invariant which involves an "outer rollback", the
  // rollback from the scope just above the current scope.

  //
  // Declarations
  //
  type Value = Interp.Value

  type Context = Interp.Context

  const EmptyCtx: Context := map[]

  datatype MState = MState(env: Environment, outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
  datatype MValue = MValue(v: Value, v': Value)
  datatype MSeqValue = MSeqValue(vs: seq<Value>, vs': seq<Value>)

  predicate EqOuterRollback(outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
  {
    EqCtx(ctx.rollback + outer_rollback, ctx'.rollback + outer_rollback')
  }

  predicate EqRolled(keys: set<string>, ctx: State, ctx': State)
  {
    EqSubCtx(keys, ctx.locals + ctx.rollback, ctx'.locals + ctx'.rollback)
  }

  predicate EqResult<V>(eq_value: (V,V) -> bool, outer_rollback: Context, res: InterpResult<V>, outer_rollback': Context, res': InterpResult<V>)
  {
    match (res, res')
      case (Success(Return(v, ctx)), Success(Return(v', ctx'))) =>
        && eq_value(v, v')
        && EqCtx(ctx.locals, ctx'.locals)
        && EqOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
      case (Failure(_), _) => true
      case _ => false
  }

  predicate EqResultValue(outer_rollback: Context, res: InterpResult<Value>, outer_rollback': Context, res': InterpResult<Value>)
  {
    EqResult(EqValue, outer_rollback, res, outer_rollback', res')
  }

  predicate EqResultSeqValue(outer_rollback: Context, res: InterpResult<seq<Value>>, outer_rollback': Context, res': InterpResult<seq<Value>>)
  {
    EqResult(EqSeqValue, outer_rollback, res, outer_rollback', res')
  }

  predicate EqResultRolled<V>(eq_value: (V,V) -> bool, keys: set<string>, res: InterpResult<V>, res': InterpResult<V>)
  {
    match (res, res')
      case (Success(Return(v, ctx)), Success(Return(v', ctx'))) =>
        && eq_value(v, v')
        && EqRolled(keys, ctx, ctx')
      case (Failure(_), _) => true
      case _ => false
  }

  predicate EqResultRolledValue(keys: set<string>, res: InterpResult<Value>, res': InterpResult<Value>)
  {
    EqResultRolled(EqValue, keys, res, res')
  }

  predicate EqResultRolledSeqValue(keys: set<string>, res: InterpResult<seq<Value>>, res': InterpResult<seq<Value>>)
  {
    EqResultRolled(EqSeqValue, keys, res, res')
  }


  predicate Inv(st: MState)
  {
    && EqCtx(st.ctx.locals, st.ctx'.locals)
    && EqOuterRollback(st.outer_rollback, st.ctx, st.outer_rollback', st.ctx')
  }

  type S(!new) = MState
  type V(!new) = MValue
  type VS(!new) = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

  predicate P(st: S, e: Expr)
  {
    var res := InterpExpr(e, st.env, st.ctx);
    var res' := InterpExpr(e, st.env, st.ctx');
    Inv(st) ==>
    EqResultValue(st.outer_rollback, res, st.outer_rollback', res')
  }
  
  predicate P_Succ(st: S, e: Expr, st': S, v: V)
  {
    && Inv(st)
    && EqResultValue(st.outer_rollback, InterpExpr(e, st.env, st.ctx), st.outer_rollback', InterpExpr(e, st.env, st.ctx'))
    && InterpExpr(e, st.env, st.ctx) == Success(Return(v.v, st'.ctx))
    && InterpExpr(e, st.env, st.ctx') == Success(Return(v.v', st'.ctx'))
    && st.env == st'.env
    && st.outer_rollback == st'.outer_rollback
    && st.outer_rollback' == st'.outer_rollback'
  }

  predicate P_Fail(st: S, e: Expr)
  {
    Inv(st) ==> InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate Pes(st: S, es: seq<Expr>)
  {
    Inv(st) ==>
    EqResultSeqValue(st.outer_rollback, InterpExprs(es, st.env, st.ctx), st.outer_rollback', InterpExprs(es, st.env, st.ctx'))
  }

  predicate Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
  {
    && Inv(st)
    && EqResultSeqValue(st.outer_rollback, InterpExprs(es, st.env, st.ctx), st.outer_rollback', InterpExprs(es, st.env, st.ctx'))
    && InterpExprs(es, st.env, st.ctx) == Success(Return(vs.vs, st'.ctx))
    && InterpExprs(es, st.env, st.ctx') == Success(Return(vs.vs', st'.ctx'))
    && st.outer_rollback == st'.outer_rollback
    && st.outer_rollback' == st'.outer_rollback'
    && st.env == st'.env
  }

  predicate Pes_Fail(st: S, es: seq<Expr>)
  {
    Inv(st) ==> InterpExprs(es, st.env, st.ctx).Failure?
  }

  function AppendValue ...
  {
    MSeqValue([v.v] + vs.vs, [v.v'] + vs.vs')
  }

  function SeqVToVS ...
  {
    if vs == [] then MSeqValue([], [])
    else
      AppendValue(MValue(vs[0].v, vs[0].v'), SeqVToVS(vs[1..]))
  }
  
  function GetNilVS ...
  {
    MSeqValue([], [])
  }

  ghost const UnitV := MValue(Values.Unit, Values.Unit)

  function VS_Last ...
  {
    var v := vs.vs[|vs.vs| - 1];
    var v' := vs.vs'[|vs.vs| - 1];
    MValue(v, v')
  }

  function GetFuel ...
  {
    st.env.fuel
  }

  function DecreaseFuel ...
  {
    var env := st.env;
    var env' := env.(fuel := env.fuel - 1);
    st.(env := env')
  }

  predicate VS_UpdateStatePre ...
  {
    && |argvs.vs| == |argvs.vs'| == |vars|
    && forall i | 0 <= i < |argvs.vs| :: EqValue(argvs.vs[i], argvs.vs'[i])
  }

  function BuildClosureCallState ...
    // Adding this precondition makes the InductAbs proofs easier
    ensures Inv(st) ==> Inv(st')
  {
    var ctx1 := BuildCallState(st.ctx.locals, vars, argvs.vs);
    var ctx1' := BuildCallState(st.ctx'.locals, vars, argvs.vs');
    var st' := MState(env, EmptyCtx, ctx1, EmptyCtx, ctx1');
    assert Inv(st) ==> Inv(st') by {
      if Inv(st) {
        reveal GEqCtx();
        BuildCallState_EqState(st.ctx.locals, st.ctx'.locals, vars, argvs.vs, argvs.vs');
        assert EqCtx(ctx1.locals, ctx1'.locals);
        assert ctx1.rollback == ctx1'.rollback == map [] by {
          reveal BuildCallState();
        }
      }
    }
    st'
  }

  function UpdateState ...
    // Adding this precondition makes the InductUpdate proofs easier
    ensures Inv(st) ==> Inv(st')
  {
    var ctx1 := st.ctx.(locals := AugmentContext(st.ctx.locals, vars, vals.vs));
    var ctx1' := st.ctx'.(locals := AugmentContext(st.ctx'.locals, vars, vals.vs'));
    var st' := MState(st.env, st.outer_rollback, ctx1, st.outer_rollback', ctx1');

    assert Inv(st) ==> Inv(st') by {
      if Inv(st) {
        reveal BuildCallState();
        reveal GEqCtx();
        BuildCallState_EqState(st.ctx.locals, st.ctx'.locals, vars, vals.vs, vals.vs');
      }
    }

    st'
  }

  function StateSaveToRollback ...
    ensures Inv(st) ==> Inv(st')
  {
    var MState(env, or, ctx, or', ctx') := st;
    var ctx1 := SaveToRollback(st.ctx, vars);
    var ctx1' := SaveToRollback(st.ctx', vars);
    var st' := MState(st.env, st.outer_rollback, ctx1, st.outer_rollback', ctx1');

    assert Inv(st) ==> Inv(st') by {
      if Inv(st) {
        var varseq := vars;
        var varset := set x | x in varseq;
        var save := map x | x in (varset * ctx.locals.Keys) - ctx.rollback.Keys :: ctx.locals[x];
        var save' := map x | x in (varset * ctx'.locals.Keys) - ctx'.rollback.Keys :: ctx'.locals[x];
        
        var ctx1 := ctx.(locals := ctx.locals - varset, rollback := ctx.rollback + save);
        var ctx1' := ctx'.(locals := ctx'.locals - varset, rollback := ctx'.rollback + save');
        
        assert ctx1 == SaveToRollback(ctx, varseq) by { reveal SaveToRollback(); }
        assert ctx1' == SaveToRollback(ctx', varseq) by { reveal SaveToRollback(); }

        assert EqCtx(ctx1.locals, ctx1'.locals) by { reveal GEqCtx(); }
        var rolled := ctx1.rollback + or;
        var rolled' := ctx1'.rollback + or';
        assert rolled.Keys == rolled'.Keys by { reveal GEqCtx(); } // Having this drastically reduces the proof time
        assert EqCtx(rolled, rolled') by { reveal GEqCtx(); } // Wow, this actually works
      }
    }

    st'
  }

  function StateStartScope ...
    ensures Inv(st) ==> Inv(st')
  {
    var ctx := StartScope(st.ctx);
    var ctx' := StartScope(st.ctx');
    reveal GEqCtx();
    MState(st.env, EmptyCtx, ctx, EmptyCtx, ctx')
  }

  function StateEndScope ...
    ensures Inv(st0) && Inv(st) && st.outer_rollback == st.outer_rollback' == EmptyCtx ==> Inv(st')
  {
    var ctx := EndScope(st0.ctx, st.ctx);
    var ctx' := EndScope(st0.ctx', st.ctx');
    reveal GEqCtx();
    MState(st.env, st0.outer_rollback, ctx, st0.outer_rollback', ctx')
  }

  function P_Step ... {
    var Return(v, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    var Return(v', ctx1') := InterpExpr(e, st.env, st.ctx').value;
    (MState(st.env, st.outer_rollback, ctx1, st.outer_rollback', ctx1'), MValue(v, v'))
  }

  function Pes_Step ... {
    var Return(vs, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    var Return(vs', ctx1') := InterpExprs(es, st.env, st.ctx').value;
    (MState(st.env, st.outer_rollback, ctx1, st.outer_rollback', ctx1'), MSeqValue(vs, vs'))
  }

  //
  // Lemmas
  //

  lemma P_Fail_Sound ... {}
  lemma P_Succ_Sound ... {}
  lemma Pes_Fail_Sound ... {}
  lemma Pes_Succ_Sound ... {}

  lemma Pes_Succ_Inj ... {}
  lemma SeqVToVS_Append ... {}

  lemma InductVar ... {
    reveal InterpExpr();
    reveal GEqCtx();

    var env := st.env;
    var v := e.name;
    
    // Start by looking in the local context
    var res0 := TryGetVariable(st.ctx.locals, v, UnboundVariable(v));
    var res0' := TryGetVariable(st.ctx'.locals, v, UnboundVariable(v));

    if res0.Success? {
      assert res0.Success?;
    }
    else {
      // Not in the local context: look in the global context
      assert v in env.globals;
      EqValue_Refl(env.globals[v]);
    }
  }

  lemma InductLiteral ... { reveal InterpExpr(); reveal InterpLiteral(); }

  lemma InductAbs ... {
    reveal InterpExpr();
    reveal EqValue_Closure();

    var MState(env, outer_rollback, ctx, outer_rollback', ctx') := st;
    var cv := Values.Closure(ctx.locals, vars, body);
    var cv' := Values.Closure(ctx'.locals, vars, body);

    forall env, argvs, argvs' |
      && |argvs| == |argvs'| == |vars|
      && (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
      ensures
        var res := InterpCallFunctionBody(cv, env, argvs);
        var res' := InterpCallFunctionBody(cv', env, argvs');
        EqPureInterpResultValue(res, res')
    {
      // The following triggers instantiations
      var argvs := MSeqValue(argvs, argvs');
      assert P(BuildClosureCallState(st, vars, body, env, argvs), body);

      reveal InterpCallFunctionBody();
    }

    assert EqValue_Closure(cv, cv');
  }

  lemma InductAbs_CallState ... {
    reveal InterpExpr();
    reveal InterpCallFunctionBody();
    reveal BuildCallState();
  }

  lemma InductExprs_Nil ... { reveal InterpExprs(); }
  lemma InductExprs_Cons ... { reveal InterpExprs(); }

  lemma InductApplyLazy_Fail ... { reveal InterpExpr(); }
  lemma InductApplyLazy_Succ ... { reveal InterpExpr(); }

  lemma InductApplyEager_Fail ... { reveal InterpExpr(); }

  lemma InductApplyEagerUnaryOp_Succ ... { reveal InterpExpr(); reveal InterpUnaryOp(); }

  lemma InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    InterpBinaryOp_Eq(e, e, op, v0.v, v1.v, v0.v', v1.v');
  }

  lemma {:fuel SeqVToVS, 2} InductApplyEagerTernaryOp_Succ ... {
    reveal InterpExpr();
    // TODO(SMH): ``SeqVToVS`` is called on literals: we shouldn't need fuel 2
    assert SeqVToVS([v0, v1, v2]) == MSeqValue([v0.v, v1.v, v2.v], [v0.v', v1.v', v2.v']);
    InterpTernaryOp_Eq(e, e, op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');
  }

  lemma InductApplyEagerBuiltinDisplay ... {
    reveal InterpExpr();
    Interp_Apply_Display_EqValue(e, e, ty.kind, argvs.vs, argvs.vs');
  }

  lemma InductApplyEagerFunctionCall ... {
    reveal InterpExpr();
    InterpFunctionCall_EqState(e, e, st.env, fv.v, fv.v', argvs.vs, argvs.vs');
  }

  lemma InductIf_Fail ... { reveal InterpExpr(); }
  lemma InductIf_Succ ... { reveal InterpExpr(); }

  lemma InductUpdate_Fail ... { reveal InterpExpr(); }
  lemma InductUpdate_Succ ... { reveal InterpExpr(); }

  lemma InductVarDecl_None_Succ ... { reveal InterpExpr(); }
  lemma InductVarDecl_Some_Fail ... { reveal InterpExpr(); }
  lemma InductVarDecl_Some_Succ  ... { reveal InterpExpr(); }

  lemma InductBind_Fail ... { reveal InterpExpr(); }
  lemma InductBind_Succ ... { reveal InterpExpr(); }

  // TODO(SMH): I tried simplifying the proofs below by adding a `requires` in ``InductBlock_Fail``
  // and ``InductBlock_Succ`` to provide the result of calling ``InterpExprs_Block_Equiv_Strong``,
  // but it didn't work due to SMT solvers' misteries.
  lemma InductBlock_Fail ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx');
  }

  lemma InductBlock_Succ ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx');
  }

  lemma InductLoop_Fail ...
  {
    reveal InterpExpr();
  }

  lemma InductLoop_Succ ...
  {
    reveal InterpExpr();
  }

} // end of module Bootstrap.Semantics.EqInterpScopes.Base


module Bootstrap.Semantics.EqInterpScopes {
  // This module derives lemmas from ``Bootstrap.Semantics.EqInterpScopes.Base``.
  
  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import opened Interp
  import opened Values
  import opened Equiv
  import opened Utils.Lib.Datatypes
  import opened Base
  import opened InterpStateIneq

  type Expr = Interp.Expr
  type Context = Interp.Context

  ghost const EqOuterRollback := Base.EqOuterRollback
  ghost const EqResultSeqValue := Base.EqResultSeqValue
  ghost const EqResultValue := Base.EqResultValue
  ghost const EqResultRolledSeqValue := Base.EqResultRolledSeqValue
  ghost const EqResultRolledValue := Base.EqResultRolledValue

  predicate EqStateOuterRollback(outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
  {
    && EqCtx(ctx.locals, ctx'.locals)
    && EqOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
  }

  predicate EqStateRolled(keys: set<string>, ctx: State, ctx': State)
  {
    && EqRolled(keys, ctx, ctx')
  }

  lemma InterpExpr_Eq(e: Expr, env: Environment, outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
    requires EqStateOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
    ensures EqResultValue(outer_rollback, InterpExpr(e, env, ctx), outer_rollback', InterpExpr(e, env, ctx'))
  {
    Base.P_Satisfied(MState(env, outer_rollback, ctx, outer_rollback', ctx'), e);
  }

  lemma InterpExprs_Eq(es: seq<Expr>, env: Environment, outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
    requires EqStateOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
    ensures EqResultSeqValue(outer_rollback, InterpExprs(es, env, ctx), outer_rollback', InterpExprs(es, env, ctx'))
  {
    Base.Pes_Satisfied(MState(env, outer_rollback, ctx, outer_rollback', ctx'), es);
  }

  lemma InterpBlock_Exprs_Eq(es: seq<Expr>, env: Environment, outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
    requires EqStateOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
    ensures EqResultValue(outer_rollback, InterpBlock_Exprs(es, env, ctx), outer_rollback', InterpBlock_Exprs(es, env, ctx'))
  {
    InterpExprs_Block_Equiv_Strong(es, env, ctx);
    InterpExprs_Block_Equiv_Strong(es, env, ctx');
    Base.Pes_Satisfied(MState(env, outer_rollback, ctx, outer_rollback', ctx'), es);

    reveal InterpExprs_Block();
  }

  predicate EqInterpBlockExprs_Single(es: seq<Expr>, es': seq<Expr>, env: Environment, keys: set<string>, ctx:State, ctx':State)
    requires EqState(ctx, ctx')
    // Rem.: we need this predicate, otherwise we don't manage to guide the instantiation in ``EqInterpBlockExprs_Inst``
  {
    EqResultRolledValue(keys, InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es', env, ctx'))
  }

  predicate StateHasKeys(ctx: State, keys: set<string>)
  {
    keys <= ctx.locals.Keys + ctx.rollback.Keys
  }

  predicate {:opaque} EqInterpBlockExprs(es: seq<Expr>, es': seq<Expr>, keys: set<string>)
  {
    (forall env, ctx:State, ctx':State | EqState(ctx, ctx') && StateHasKeys(ctx, keys) && StateHasKeys(ctx', keys) ::
       EqInterpBlockExprs_Single(es, es', env, keys, ctx, ctx'))
  }

  lemma EqInterpBlockExprs_Inst(es: seq<Expr>, es': seq<Expr>, env: Environment, keys: set<string>, ctx: State, ctx': State)
    requires EqInterpBlockExprs(es, es', keys)
    requires EqState(ctx, ctx')
    requires StateHasKeys(ctx, keys)
    requires StateHasKeys(ctx', keys)
    ensures EqResultRolledValue(keys, InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es', env, ctx'))
  {
    reveal EqInterpBlockExprs();
    assert EqInterpBlockExprs_Single(es, es', env, keys, ctx, ctx');
  }

  lemma InterpBlock_Exprs_Eq_Append(
    e: Expr, tl: seq<Expr>, tl': seq<Expr>, env: Environment, keys: set<string>, ctx: State, ctx': State)
    requires EqState(ctx, ctx')
    requires StateHasKeys(ctx, keys)
    requires StateHasKeys(ctx', keys)
    requires EqInterpBlockExprs(tl, tl', keys)
    requires |tl| > 0
    ensures EqResultRolledValue(keys, InterpBlock_Exprs([e] + tl, env, ctx), InterpBlock_Exprs([e] + tl', env, ctx'))
    // Auxiliary lemma for the proofs about transformations operating on blocks. This is especially
    // useful when those transformations might update the length of the sequence of expressions
    // in the blocks. The proof is a bit tricky, because the case where the sequence has length 1
    // is a special case in the definition of ``EqInterpBlock_Exprs``.
  {
    var es := [e] + tl;
    assert e == es[0];

    reveal InterpBlock_Exprs();

    // Evaluate the first expression
    var res0 := InterpExprWithType(e, Types.Unit, env, ctx);
    var res0' := InterpExprWithType(e, Types.Unit, env, ctx');
    assert EqStateOuterRollback(map [], ctx, map [], ctx') by { reveal GEqCtx(); }
    InterpExpr_Eq(e, env, map [], ctx, map [], ctx');
    InterpExpr_StateSmaller(e, env, ctx);
    InterpExpr_StateSmaller(e, env, ctx');

    // We need to make a case disjunction on whether the length of the concatenated sequences is
    // > 1 or not
    if |tl'| >= 1 {
      // The "regular" case

      // Evaluate the remaining expressions
      if res0.Success? && res0.value.ret == Interp.V.Unit {
        var Return(_, ctx0) := res0.value;
        var Return(_, ctx0') := res0'.value;

        var res1 := InterpBlock_Exprs(tl, env, ctx0);
        var res1' := InterpBlock_Exprs(tl', env, ctx0');

        assert EqState(ctx0, ctx0') by { reveal GEqCtx(); }
        EqInterpBlockExprs_Inst(tl, tl', env, keys, ctx0, ctx0');
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

        if v == Interp.V.Unit {
          assert v' == Interp.V.Unit;
          assert EqState(ctx0, ctx0') by { reveal GEqCtx(); }
          EqInterpBlockExprs_Inst(tl, tl', env, keys, ctx0, ctx0');
        }
        else {
          // Trivial case:
          assert v' != Interp.V.Unit;
          var res := InterpBlock_Exprs([e] + tl, env, ctx);
          assert res.Failure?;
        }
      }
      else {
        // Trivial
      }
    }
  }

} // end of module Bootstrap.Semantics.EqInterpScopes

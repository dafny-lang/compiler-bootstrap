include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "Interp.dfy"
include "Equiv.dfy"
include "ExprInduction.dfy"

module Bootstrap.Semantics.EqInterpRefl {

module Base refines ExprInduction.Ind {
  //
  // Declarations
  //
  type Value = Interp.Value

  datatype MState = MState(env: Environment, ctx: State, ctx': State)
  datatype MValue = MValue(v: Value, v': Value)
  datatype MSeqValue = MSeqValue(vs: seq<Value>, vs': seq<Value>)

  type S(!new) = MState
  type V(!new) = MValue
  type VS(!new) = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

  predicate P(st: S, e: Expr)
  {
    EqState(st.ctx, st.ctx') ==>
    EqInterpResultValue(InterpExpr(e, st.env, st.ctx), InterpExpr(e, st.env, st.ctx'))
  }
  
  predicate P_Succ(st: S, e: Expr, st': S, v: V)
  {
    && EqState(st.ctx, st.ctx')
    && EqInterpResultValue(InterpExpr(e, st.env, st.ctx), InterpExpr(e, st.env, st.ctx'))
    && InterpExpr(e, st.env, st.ctx) == Success(Return(v.v, st'.ctx))
    && InterpExpr(e, st.env, st.ctx') == Success(Return(v.v', st'.ctx'))
    && st.env == st'.env
  }

  predicate P_Fail(st: S, e: Expr)
  {
    EqState(st.ctx, st.ctx') ==> InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate Pes(st: S, es: seq<Expr>)
  {
    EqState(st.ctx, st.ctx') ==>
    EqInterpResultSeqValue(InterpExprs(es, st.env, st.ctx), InterpExprs(es, st.env, st.ctx'))
  }

  predicate Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
  {
    && EqState(st.ctx, st.ctx')
    && EqInterpResultSeqValue(InterpExprs(es, st.env, st.ctx), InterpExprs(es, st.env, st.ctx'))
    && InterpExprs(es, st.env, st.ctx) == Success(Return(vs.vs, st'.ctx))
    && InterpExprs(es, st.env, st.ctx') == Success(Return(vs.vs', st'.ctx'))
    && st.env == st'.env
  }

  predicate Pes_Fail(st: S, es: seq<Expr>)
  {
    !EqState(st.ctx, st.ctx') || InterpExprs(es, st.env, st.ctx).Failure?
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

  predicate VS_UpdateStatePre ...
  {
    && |argvs.vs| == |argvs.vs'| == |vars|
    && forall i | 0 <= i < |argvs.vs| :: EqValue(argvs.vs[i], argvs.vs'[i])
  }

  function BuildClosureCallState ...
    // Adding this precondition makes the InductAbs proofs easier
    ensures
      EqState(st.ctx, st.ctx') ==>
      EqState(st'.ctx, st'.ctx')
  {
    var ctx1 := BuildCallState(st.ctx.locals, vars, argvs.vs);
    var ctx1' := BuildCallState(st.ctx'.locals, vars, argvs.vs');
    var st' := MState(env, ctx1, ctx1');
    assert EqState(st.ctx, st.ctx') ==> EqState(st'.ctx, st'.ctx') by {
      if EqState(st.ctx, st.ctx') {
        BuildCallState_EqState(st.ctx.locals, st.ctx'.locals, vars, argvs.vs, argvs.vs');
      }
    }
    st'
  }

  function UpdateState ...
    // Adding this precondition makes the InductUpdate proofs easier
    ensures
      EqState(st.ctx, st.ctx') ==>
      EqState(st'.ctx, st'.ctx')
  {
    var ctx1 := st.ctx.(locals := AugmentContext(st.ctx.locals, vars, vals.vs));
    var ctx1' := st.ctx'.(locals := AugmentContext(st.ctx'.locals, vars, vals.vs'));
    var st' := MState(st.env, ctx1, ctx1');

    assert EqState(st.ctx, st.ctx') ==> EqState(st'.ctx, st'.ctx') by {
      if EqState(st.ctx, st.ctx') {
        BuildCallState_EqState(st.ctx.locals, st.ctx'.locals, vars, vals.vs, vals.vs'); // TODO: remove?
        reveal BuildCallState();
      }
    }

    st'
  }

  function StateSaveToRollback ...
    ensures EqState(st.ctx, st.ctx') ==> EqState(st'.ctx, st'.ctx')
  {
    var ctx := SaveToRollback(st.ctx, vars);
    var ctx' := SaveToRollback(st.ctx', vars);
    var st' := MState(st.env, ctx, ctx');

    reveal GEqCtx();
    assert EqState(st.ctx, st.ctx') ==> EqState(st'.ctx, st'.ctx') by {
      if EqState(st.ctx, st.ctx') {
        SaveToRollback_Equiv(st.ctx, st.ctx', vars);
      }
    }

    st'
  }

  function StateStartScope ...
    ensures EqState(st.ctx, st.ctx') ==> EqState(st'.ctx, st'.ctx')
  {
    var ctx := StartScope(st.ctx);
    var ctx' := StartScope(st.ctx');
    reveal GEqCtx();
    MState(st.env, ctx, ctx')
  }

  function StateEndScope ...
    ensures EqState(st0.ctx, st0.ctx') && EqState(st.ctx, st.ctx') ==> EqState(st'.ctx, st'.ctx')
  {
    var ctx := EndScope(st0.ctx, st.ctx);
    var ctx' := EndScope(st0.ctx', st.ctx');
    reveal GEqCtx();
    MState(st.env, ctx, ctx')
  }

  function P_Step ... {
    var Return(v, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    var Return(v', ctx1') := InterpExpr(e, st.env, st.ctx').value;
    (MState(st.env, ctx1, ctx1'), MValue(v, v'))
  }

  function Pes_Step ... {
    var Return(vs, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    var Return(vs', ctx1') := InterpExprs(es, st.env, st.ctx').value;
    (MState(st.env, ctx1, ctx1'), MSeqValue(vs, vs'))
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

    var MState(env, ctx, ctx') := st;
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

  lemma InductApplyLazy_Fail ... { reveal InterpExpr(); reveal InterpLazy(); }
  lemma InductApplyLazy_Succ ... { reveal InterpExpr(); reveal InterpLazy(); }

  lemma InductApplyEager_Fail ... { reveal InterpExpr(); }

  lemma InductApplyEagerUnaryOp_Succ ... { reveal InterpExpr(); reveal InterpUnaryOp(); }

  lemma InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    InterpBinaryOp_Eq(e, e, op, v0.v, v1.v, v0.v', v1.v');
  }

  lemma InductApplyEagerTernaryOp_Succ ... {
    reveal InterpExpr();
    reveal InterpTernaryOp();

    // TODO: using this lemma makes Dafny crash:
    // InterpTernaryOp_Eq(e, e, op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');

    EqValue_HasEqValue_Eq(v0.v, v0.v');
    EqValue_HasEqValue_Eq(v1.v, v1.v');
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

  // TODO(SMH): I tried simplifying the proofs below by adding a `requires` in ``InductBlock_Fail``
  // and ``InductBlock_Succ`` to provide the assertions and the results of calling the lemmas used
  // in the proof below, but it didn't work due to SMT solvers' misteries.
  lemma InductBlock_Fail ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();

    var env := st.env;

    // We need this because of the fuel
    assert InterpExpr(e, env, st.ctx) == InterpBlock(stmts, env, st.ctx);
    assert InterpExpr(e, env, st.ctx') == InterpBlock(stmts, env, st.ctx');
    
    InterpExprs_Block_Equiv_Strong(stmts, env, st_start.ctx);
    InterpExprs_Block_Equiv_Strong(stmts, env, st_start.ctx');
  }

  // TODO(SMH): try with this: {:fuel InterpBlock,2}
  lemma InductBlock_Succ ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();

    var env := st.env;

    // We need this because of the fuel
    assert InterpExpr(e, env, st.ctx) == InterpBlock(stmts, env, st.ctx);
    assert InterpExpr(e, env, st.ctx') == InterpBlock(stmts, env, st.ctx');
    
    InterpExprs_Block_Equiv_Strong(stmts, env, st_start.ctx);
    InterpExprs_Block_Equiv_Strong(stmts, env, st_start.ctx');
  }

} // end of module Bootstrap.Semantics.EqInterpRefl.Base

  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import opened Interp
  import opened Values
  import opened Equiv
  import opened Utils.Lib.Datatypes
  import opened Base

  type Expr = Interp.Expr

  lemma InterpBlock_Exprs_EqRefl(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
    // TODO(SMH): for some reason, using ``Seq_All`` makes some proofs fail. The weird thing is
    // that I can then prove `Seq_All(SupportsInterp, es)` in an assertion just before the call
    // to the lemma, but the lemma precondition keeps failing.
    requires forall e | e in es :: SupportsInterp(e)
    requires EqState(ctx, ctx')
    ensures EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es, env, ctx'))
  {
    InterpExprs_Block_Equiv_Strong(es, env, ctx);
    InterpExprs_Block_Equiv_Strong(es, env, ctx');
    Base.Pes_Satisfied(MState(env, ctx, ctx'), es);

    reveal InterpExprs_Block();
  }

  lemma InterpExprs_EqRefl(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
    requires EqState(ctx, ctx')
    ensures EqInterpResultSeqValue(InterpExprs(es, env, ctx), InterpExprs(es, env, ctx'))
  {
    Base.Pes_Satisfied(MState(env, ctx, ctx'), es);
  }

  // DISCUSS: the proof actually indirectly relies on the fact that ``EqValue`` is reflexive.
  // But the proof that ``EqValue`` is reflexive (not done) relies, for the closure case, on the fact
  // that ``InterpExpr`` is reflexive. The termination argument is not trivial, and we may have to
  // rely on step-indexing.
  //
  // Here is an old comment, which gives some insight about what is going on:
  //
  // Actually the proof of termination is an issue in the case we lookup a global
  // variable, because the global environment always stays the same...
  //
  // I think we could do the proof as follows:
  // - define an EqValueN relation which is parameterized by a fuel (which is used for
  //   the closures - and thus not quantified in EqValue_Closure)
  // - for the closures, the EqValue applied on the returned results would use the fuel
  //   remaining after the bodies have been executed (this would solve the problem of
  //   proving reflexivity about the values in the environment, when looking up globals,
  //   in particular)
  // - prove the reflexivity for EqValueN: forall v n. EqValueN(v, v, n)
  // - from this theorem, we should be able to prove the reflexivity theorem. The tricky
  //   case is for closures, in which case we should use the fact that:
  //
  //   forall fuel fuel' ::
  //     var res := Interp(..., fuel);
  //     var res' := Interp(..., fuel');
  //     res.Success? ==>
  //       fuel' >= fuel - res.ctx.fuel ==>
  //         res'.Success? && res'.ctx.fuel == fuel' - (fuel - res.ctx.fuel)
  //
  //   This way, we would be able to properly instantiate the initial fuel to get:
  //   
  //   forall n. EqInterpResultValueN(..., n)
  //
  //   Finally, we would get: EqInterpResultValue(...) by using the induction hypothesis
  //   (where termination is given by the fact that the type of the return value is smaller
  //   than the type of the closure).
  lemma InterpExpr_EqRefl(e: Expr, env: Environment, ctx: State, ctx': State)
    requires EqState(ctx, ctx')
    ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e, env, ctx'))
  {
    Base.P_Satisfied(MState(env, ctx, ctx'), e);
  }

} // end of module Bootstrap.Semantics.EqInterpRefl

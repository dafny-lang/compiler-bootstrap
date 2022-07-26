include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "Interp.dfy"
include "Equiv.dfy"
include "ExprInduction.dfy"

module Bootstrap.Semantics.EqInterpScopes {
// TODO(SMH): this can be factorized with EqInterpRefl (the results we prove here are strictly stronger
// than what we prove in EqInterpRefl actually).

module Base refines ExprInduction.Ind {
  // Prove that it is ok not to enter a scope

  //
  // Declarations
  //
  type {:verify false} Value = Interp.Value

  type {:verify false} Context = Interp.Context

  const {:verify false} EmptyCtx: Context := map[]

  datatype {:verify false} MState = MState(env: Environment, outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
  datatype {:verify false} MValue = MValue(v: Value, v': Value)
  datatype {:verify false} MSeqValue = MSeqValue(vs: seq<Value>, vs': seq<Value>)

  predicate {:verify false} EqOuterRollback(outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
  {
    EqCtx(ctx.rollback + outer_rollback, ctx'.rollback + outer_rollback')
  }

  // TODO(SMH): move? This is not used in this module. But this should be kept with ``EqOuterRollback``
  predicate {:verify true} EqRolled(ctx: State, ctx': State)
  {
    EqCtx(ctx.locals + ctx.rollback, ctx'.locals + ctx'.rollback)
  }

  predicate {:verify false} EqResult<V>(eq_value: (V,V) -> bool, outer_rollback: Context, res: InterpResult<V>, outer_rollback': Context, res': InterpResult<V>)
  {
    match (res, res')
      case (Success(Return(v, ctx)), Success(Return(v', ctx'))) =>
        && eq_value(v, v')
        && EqCtx(ctx.locals, ctx'.locals)
        && EqOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
      case (Failure(_), _) => true
      case _ => false
  }

  predicate {:verify false} EqResultValue(outer_rollback: Context, res: InterpResult<Value>, outer_rollback': Context, res': InterpResult<Value>)
  {
    EqResult(EqValue, outer_rollback, res, outer_rollback', res')
  }

  predicate {:verify false} EqResultSeqValue(outer_rollback: Context, res: InterpResult<seq<Value>>, outer_rollback': Context, res': InterpResult<seq<Value>>)
  {
    EqResult(EqSeqValue, outer_rollback, res, outer_rollback', res')
  }

  // TODO(SMH): factorize with EqResult and move. The annoying thing is that functions are not curried...
  predicate {:verify true} EqResultRolled<V>(eq_value: (V,V) -> bool, res: InterpResult<V>, res': InterpResult<V>)
  {
    match (res, res')
      case (Success(Return(v, ctx)), Success(Return(v', ctx'))) =>
        && eq_value(v, v')
        && EqRolled(ctx, ctx')
      case (Failure(_), _) => true
      case _ => false
  }

  predicate {:verify true} EqResultRolledValue(res: InterpResult<Value>, res': InterpResult<Value>)
  {
    EqResultRolled(EqValue, res, res')
  }

  predicate {:verify true} EqResultRolledSeqValue(res: InterpResult<seq<Value>>, res': InterpResult<seq<Value>>)
  {
    EqResultRolled(EqSeqValue, res, res')
  }


  predicate {:verify false} Inv(st: MState)
  {
    && EqCtx(st.ctx.locals, st.ctx'.locals)
    && EqOuterRollback(st.outer_rollback, st.ctx, st.outer_rollback', st.ctx')
  }

  type {:verify false} S(!new) = MState
  type {:verify false} V(!new) = MValue
  type {:verify false} VS(!new) = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

  predicate {:verify false} P(st: S, e: Expr)
  {
    var res := InterpExpr(e, st.env, st.ctx);
    var res' := InterpExpr(e, st.env, st.ctx');
    Inv(st) ==>
    EqResultValue(st.outer_rollback, res, st.outer_rollback', res')
  }
  
  predicate {:verify false} P_Succ(st: S, e: Expr, st': S, v: V)
  {
    && Inv(st)
    && EqResultValue(st.outer_rollback, InterpExpr(e, st.env, st.ctx), st.outer_rollback', InterpExpr(e, st.env, st.ctx'))
    && InterpExpr(e, st.env, st.ctx) == Success(Return(v.v, st'.ctx))
    && InterpExpr(e, st.env, st.ctx') == Success(Return(v.v', st'.ctx'))
    && st.env == st'.env
    && st.outer_rollback == st'.outer_rollback
    && st.outer_rollback' == st'.outer_rollback'
  }

  predicate {:verify false} P_Fail(st: S, e: Expr)
  {
    Inv(st) ==> InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate {:verify false} Pes(st: S, es: seq<Expr>)
  {
    Inv(st) ==>
    EqResultSeqValue(st.outer_rollback, InterpExprs(es, st.env, st.ctx), st.outer_rollback', InterpExprs(es, st.env, st.ctx'))
  }

  predicate {:verify false} Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
  {
    && Inv(st)
    && EqResultSeqValue(st.outer_rollback, InterpExprs(es, st.env, st.ctx), st.outer_rollback', InterpExprs(es, st.env, st.ctx'))
    && InterpExprs(es, st.env, st.ctx) == Success(Return(vs.vs, st'.ctx))
    && InterpExprs(es, st.env, st.ctx') == Success(Return(vs.vs', st'.ctx'))
    && st.outer_rollback == st'.outer_rollback
    && st.outer_rollback' == st'.outer_rollback'
    && st.env == st'.env
  }

  predicate {:verify false} Pes_Fail(st: S, es: seq<Expr>)
  {
    Inv(st) ==> InterpExprs(es, st.env, st.ctx).Failure?
  }

  function {:verify false} AppendValue ...
  {
    MSeqValue([v.v] + vs.vs, [v.v'] + vs.vs')
  }

  function {:verify false} SeqVToVS ...
  {
    if vs == [] then MSeqValue([], [])
    else
      AppendValue(MValue(vs[0].v, vs[0].v'), SeqVToVS(vs[1..]))
  }
  
  function {:verify false} GetNilVS ...
  {
    MSeqValue([], [])
  }

  ghost const {:verify false} UnitV := MValue(Values.Unit, Values.Unit)

  function {:verify false} VS_Last ...
  {
    var v := vs.vs[|vs.vs| - 1];
    var v' := vs.vs'[|vs.vs| - 1];
    MValue(v, v')
  }

  predicate {:verify false} VS_UpdateStatePre ...
  {
    && |argvs.vs| == |argvs.vs'| == |vars|
    && forall i | 0 <= i < |argvs.vs| :: EqValue(argvs.vs[i], argvs.vs'[i])
  }

  function {:verify false} BuildClosureCallState ...
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

  function {:verify false} UpdateState ...
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

  function {:verify false} StateSaveToRollback ...
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
        assert rolled.Keys == rolled'.Keys by { reveal GEqCtx(); } // This helps reduce the proof time
        assert EqCtx(rolled, rolled') by { reveal GEqCtx(); } // Wow, this actually works
      }
    }

    st'
  }

  function {:verify false} StateStartScope ...
    ensures Inv(st) ==> Inv(st')
  {
    var ctx := StartScope(st.ctx);
    var ctx' := StartScope(st.ctx');
    reveal GEqCtx();
    MState(st.env, EmptyCtx, ctx, EmptyCtx, ctx')
  }

  function {:verify false} StateEndScope ...
    ensures Inv(st0) && Inv(st) && st.outer_rollback == st.outer_rollback' == EmptyCtx ==> Inv(st')
  {
    var ctx := EndScope(st0.ctx, st.ctx);
    var ctx' := EndScope(st0.ctx', st.ctx');
    reveal GEqCtx();
    MState(st.env, st0.outer_rollback, ctx, st0.outer_rollback', ctx')
  }

  function {:verify false} P_Step ... {
    var Return(v, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    var Return(v', ctx1') := InterpExpr(e, st.env, st.ctx').value;
    (MState(st.env, st.outer_rollback, ctx1, st.outer_rollback', ctx1'), MValue(v, v'))
  }

  function {:verify false} Pes_Step ... {
    var Return(vs, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    var Return(vs', ctx1') := InterpExprs(es, st.env, st.ctx').value;
    (MState(st.env, st.outer_rollback, ctx1, st.outer_rollback', ctx1'), MSeqValue(vs, vs'))
  }

  //
  // Lemmas
  //

  lemma {:verify false} P_Fail_Sound ... {}
  lemma {:verify false} P_Succ_Sound ... {}
  lemma {:verify false} Pes_Fail_Sound ... {}
  lemma {:verify false} Pes_Succ_Sound ... {}

  lemma {:verify false} Pes_Succ_Inj ... {}
  lemma {:verify false} SeqVToVS_Append ... {}

  lemma {:verify false} InductVar ... {
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

  lemma {:verify false} InductLiteral ... { reveal InterpExpr(); reveal InterpLiteral(); }

  lemma {:verify false} InductAbs ... {
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

  lemma {:verify false} InductAbs_CallState ... {
    reveal InterpExpr();
    reveal InterpCallFunctionBody();
    reveal BuildCallState();
  }

  lemma {:verify false} InductExprs_Nil ... { reveal InterpExprs(); }
  lemma {:verify false} InductExprs_Cons ... { reveal InterpExprs(); }

  lemma {:verify false} InductApplyLazy_Fail ... { reveal InterpExpr(); reveal InterpLazy(); }
  lemma {:verify false} InductApplyLazy_Succ ... { reveal InterpExpr(); reveal InterpLazy(); }

  lemma {:verify false} InductApplyEager_Fail ... { reveal InterpExpr(); }

  lemma {:verify false} InductApplyEagerUnaryOp_Succ ... { reveal InterpExpr(); reveal InterpUnaryOp(); }

  lemma {:verify false} InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    InterpBinaryOp_Eq(e, e, op, v0.v, v1.v, v0.v', v1.v');
  }

  lemma {:verify false} InductApplyEagerTernaryOp_Succ ... {
    reveal InterpExpr();
    reveal InterpTernaryOp();

    // TODO: using this lemma makes Dafny crash:
    // InterpTernaryOp_Eq(e, e, op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');

    EqValue_HasEqValue_Eq(v0.v, v0.v');
    EqValue_HasEqValue_Eq(v1.v, v1.v');
  }

  lemma {:verify false} InductApplyEagerBuiltinDisplay ... {
    reveal InterpExpr();
    Interp_Apply_Display_EqValue(e, e, ty.kind, argvs.vs, argvs.vs');
  }

  lemma {:verify false} InductApplyEagerFunctionCall ... {
    reveal InterpExpr();
    InterpFunctionCall_EqState(e, e, st.env, fv.v, fv.v', argvs.vs, argvs.vs');
  }

  lemma {:verify false} InductIf_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductIf_Succ ... { reveal InterpExpr(); }

  lemma {:verify false} InductUpdate_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductUpdate_Succ ... { reveal InterpExpr(); }

  lemma {:verify false} InductVarDecl_None_Succ ... { reveal InterpExpr(); }
  lemma {:verify false} InductVarDecl_Some_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductVarDecl_Some_Succ  ... { reveal InterpExpr(); }

  // TODO(SMH): I tried simplifying the proofs below by adding a `requires` in ``InductBlock_Fail``
  // and ``InductBlock_Succ`` to provide the assertions and the results of calling the lemmas used
  // in the proof below, but it didn't work due to SMT solvers' misteries.
  lemma {:verify false} InductBlock_Fail ...
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

  lemma {:verify false} InductBlock_Succ ...
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

} // end of module Bootstrap.Semantics.EqInterpScopes.Base

  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import opened Interp
  import opened Values
  import opened Equiv
  import opened Utils.Lib.Datatypes
  import opened Base

  type {:verify false} Expr = Interp.Expr
  type {:verify false} Context = Interp.Context

  ghost const {:verify false} EqOuterRollback := Base.EqOuterRollback
  ghost const {:verify false} EqResultSeqValue := Base.EqResultSeqValue
  ghost const {:verify false} EqResultValue := Base.EqResultValue
  ghost const {:verify false} EqResultRolledSeqValue := Base.EqResultRolledSeqValue
  ghost const {:verify false} EqResultRolledValue := Base.EqResultRolledValue

  predicate EqStateOuterRollback(outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
  {
    && EqCtx(ctx.locals, ctx'.locals)
    && EqOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
  }

  predicate EqStateRolled(ctx: State, ctx': State)
  {
    && EqRolled(ctx, ctx')
  }

  lemma {:verify false} InterpExpr_Eq(e: Expr, env: Environment, outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
    requires EqStateOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
    ensures EqResultValue(outer_rollback, InterpExpr(e, env, ctx), outer_rollback', InterpExpr(e, env, ctx'))
  {
    Base.P_Satisfied(MState(env, outer_rollback, ctx, outer_rollback', ctx'), e);
  }

  lemma {:verify false} InterpExprs_Eq(es: seq<Expr>, env: Environment, outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
    requires EqStateOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
    ensures EqResultSeqValue(outer_rollback, InterpExprs(es, env, ctx), outer_rollback', InterpExprs(es, env, ctx'))
  {
    Base.Pes_Satisfied(MState(env, outer_rollback, ctx, outer_rollback', ctx'), es);
  }

  lemma {:verify false} InterpBlock_Exprs_Eq(es: seq<Expr>, env: Environment, outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
    requires EqStateOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
    ensures EqResultValue(outer_rollback, InterpBlock_Exprs(es, env, ctx), outer_rollback', InterpBlock_Exprs(es, env, ctx'))
  {
    InterpExprs_Block_Equiv_Strong(es, env, ctx);
    InterpExprs_Block_Equiv_Strong(es, env, ctx');
    Base.Pes_Satisfied(MState(env, outer_rollback, ctx, outer_rollback', ctx'), es);

    reveal InterpExprs_Block();
  }

  predicate EqInterpBlockExprs_Single(es: seq<Exprs.T>, es': seq<Exprs.T>, env: Environment, ctx:State, ctx':State)
    requires Seq_All(SupportsInterp, es)
    requires Seq_All(SupportsInterp, es')
    requires EqState(ctx, ctx')
    // Rk.: we need this predicate, otherwise we don't manage to guide the instantiation in ``EqInterpBlockExprs_Inst``
  {
    EqResultRolledValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es', env, ctx'))
  }

  predicate {:opaque} {:verify true} EqInterpBlockExprs(es: seq<Exprs.T>, es': seq<Exprs.T>)
  {
    Seq_All(SupportsInterp, es) ==>
    (&& Seq_All(SupportsInterp, es')
     && (forall env, ctx:State, ctx':State | EqState(ctx, ctx') ::
        EqInterpBlockExprs_Single(es, es', env, ctx, ctx')))
  }

  lemma {:verify true} EqInterpBlockExprs_Inst(es: seq<Exprs.T>, es': seq<Exprs.T>, env: Environment, ctx: State, ctx': State)
    requires EqInterpBlockExprs(es, es')
    requires Seq_All(SupportsInterp, es)
    requires EqState(ctx, ctx')
    ensures Seq_All(SupportsInterp, es')
    ensures EqResultRolledValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es', env, ctx'))
  {
    reveal EqInterpBlockExprs();
    assert EqInterpBlockExprs_Single(es, es', env, ctx, ctx');
  }

  lemma {:verify true} InterpBlock_Exprs_Eq_Append(
    e: Expr, tl: seq<Expr>, tl': seq<Expr>, env: Environment, ctx: State, ctx': State)
    requires SupportsInterp(e)
//    requires Seq_All(SupportsInterp, tl)
//    requires Seq_All(SupportsInterp, tl')
    requires forall e | e in tl :: SupportsInterp(e)
    requires forall e | e in tl' :: SupportsInterp(e)
    requires EqState(ctx, ctx')
    requires EqInterpBlockExprs(tl, tl')
    requires |tl| > 0
    ensures EqResultRolledValue(InterpBlock_Exprs([e] + tl, env, ctx), InterpBlock_Exprs([e] + tl', env, ctx'))
    // Auxiliary lemma for the proofs about transformations operating on blocks. This is especially
    // useful when those transformations might update the length of the sequence of expressions
    // in the blocks. The proof is a bit tricky, because the case where the sequence has length 1
    // is a special case in the definition of ``EqInterpBlock_Exprs``.
    //
    // - `or`, `or'` : outer rollback
  {
    var es := [e] + tl;
    assert e == es[0];

    reveal InterpBlock_Exprs();

    // Evaluate the first expression
    var res0 := InterpExprWithType(e, Types.Unit, env, ctx);
    var res0' := InterpExprWithType(e, Types.Unit, env, ctx');
    assert EqStateOuterRollback(map [], ctx, map [], ctx') by { reveal GEqCtx(); }
    InterpExpr_Eq(e, env, map [], ctx, map [], ctx');

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

        if v == Interp.V.Unit {
          assert v' == Interp.V.Unit;
          assert EqState(ctx0, ctx0') by { reveal GEqCtx(); }
          EqInterpBlockExprs_Inst(tl, tl', env, ctx0, ctx0');
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

/*  lemma InterpBlock_Exprs_Eq_Append(e: Expr, e': Expr, tl: seq<Expr>, tl': seq<Expr>, env: Environment, ctx: State, ctx': State)
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
    var res0 := InterpExprWithType(e, Types.Unit, env, ctx);
    var res0' := InterpExprWithType(e', Types.Unit, env, ctx');
    EqInterp_Inst(e, e', env, ctx, ctx');

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
          // Trivial case:
          assert v' != V.Unit;
          var res := InterpBlock_Exprs([e] + tl, env, ctx);
          assert res.Failure?;
        }
      }
      else {
        // Trivial
      }
    }
  } */


} // end of module Bootstrap.Semantics.EqInterpScopes

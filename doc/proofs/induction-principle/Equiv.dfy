include "Utils.dfy"
include "AST.dfy"
include "Interp.dfy"
include "Induction.dfy"

module Equiv refines Induction {
  // A trivial example of the induction principle - mostly a sanity check.

  import opened Interp

  // Introducing predicates to make reasoning harder and mimick the "real" Dind
  // proofs.
  predicate EqValue(x: int, y: int)
  {
    x == y
  }

  predicate {:opaque} EqCtx(ctx: Context, ctx': Context)
  {
    && ctx.Keys == ctx'.Keys
    && forall x | x in ctx.Keys :: ctx[x] == ctx'[x]
  }

  predicate EqResult(res: InterpResult, res': InterpResult)
  {
    match (res, res')
      case (Success((v, ctx)), Success((v', ctx'))) =>
        && EqValue(v, v')
        && EqCtx(ctx, ctx')
      case (Failure, _) =>
        true
      case _ =>
        false
  }

  //
  // Below, we prove that if we evaluate an expression starting from equivalent contexts,
  // then we evaluate to equivalent results.
  //

  datatype MState = MState(ctx: Context, ctx': Context)
  datatype MValue = MValue(v: int, v': int)

  type S = MState
  type V = MValue

  ghost const Zero: V := MValue(0, 0)

  predicate Inv(st: MState)
  {
    && EqCtx(st.ctx, st.ctx')
  }

  predicate P ...
  {
    var res := InterpExpr(e, st.ctx);
    var res' := InterpExpr(e, st.ctx');
    Inv(st) ==>
    EqResult(res, res')
  }

  predicate P_Succ ...
  {
    var res := InterpExpr(e, st.ctx);
    var res' := InterpExpr(e, st.ctx');
    && Inv(st)
    && EqResult(res, res')
    && res == Success((v.v, st'.ctx))
    && res' == Success((v.v', st'.ctx'))
  }

  predicate P_Fail ...
  {
    Inv(st) ==> InterpExpr(e, st.ctx).Failure?
  }

  function AssignState ...
    ensures Inv(st) && EqValue(val.v, val.v') ==> Inv(st')
  {
    var MState(ctx, ctx') := st;
    var ctx1 := ctx[v := val.v];
    var ctx1' := ctx'[v := val.v'];
    var st' := MState(ctx1, ctx1');

    var b := Inv(st) && EqValue(val.v, val.v');
    assert b ==> Inv(st') by {
      if b {
        reveal EqCtx();
      }
    }

    st'
  }

  function BindStartScope ...
    ensures Inv(st) && EqValue(val.v, val.v') ==> Inv(st')
  {
    AssignState(st, v, val)
  }

  function BindEndScope ...
    ensures Inv(st0) && Inv(st) ==> Inv(st')
  {
    var MState(ctx0, ctx0') := st0;
    var MState(ctx, ctx') := st;
    var ctx1 := ctx0 + (ctx - {v});
    var ctx1' := ctx0' + (ctx' - {v});
    var st' := MState(ctx1, ctx1');

    var b := Inv(st0) && Inv(st);
    assert b ==> Inv(st') by {
      if b {
        reveal EqCtx();
      }
    }

    st'
  }

  function P_Step ...
  {
    var Success((v, ctx1)) := InterpExpr(e, st.ctx);
    var Success((v', ctx1')) := InterpExpr(e, st.ctx');
    (MState(ctx1, ctx1'), MValue(v, v'))
  }

  lemma P_Fail_Sound ... {}
  lemma P_Succ_Sound ... {}
  lemma InductVar ... { reveal EqCtx(); }
  lemma InductLiteral ... {}
  lemma InductIf_Fail ... {}
  lemma InductIf_Succ ... {}
  lemma InductOp_Fail ... {}
  lemma InductOp_Succ ... {}
  lemma InductSeq_Fail ... {}
  lemma InductSeq_Succ ... {}
  lemma InductAssign_Fail ... {}
  lemma InductAssign_Succ ... { reveal EqCtx(); }

  lemma InductBind_Fail ...  {}
  lemma InductBind_Succ ... { reveal EqCtx(); }
}

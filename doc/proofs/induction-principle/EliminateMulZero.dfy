include "Utils.dfy"
include "AST.dfy"
include "Interp.dfy"
include "Induction.dfy"
include "Pure.dfy"

module EliminateMulZero refines Induction {
  // This small transformation eliminates multiplications by 0:
  //
  //  `x * 0 --> 0`
  //  `0 * x --> 0`
  //
  // Of course, we need to check that `x` is pure before eliminating it.
  //
  // Rk.: what helps us a lot in the proofs is that we can use the native equality,
  // because there are no closures.

  import opened Interp
  import Pure

  const ZeroExpr: Expr := Literal(0)

  predicate method IsZeroMulPure(e1: Expr, e2: Expr)
  {
    && e1 == ZeroExpr
    && Pure.IsPure(e2)
  }

  function method Eliminate(e: Expr): Expr
    decreases e
  {
    match e
      case Var(name) => e
      case Literal(n) => e
      case Bind(bvar, bval, body) =>
        var bval' := Eliminate(bval);
        var body' := Eliminate(body);
        Bind(bvar, bval', body')
      case Assign(avar, aval) =>
        var aval' := Eliminate(aval);
        Assign(avar, aval')
      case If(cond, thn, els) =>
        var cond' := Eliminate(cond);
        var thn' := Eliminate(thn);
        var els' := Eliminate(els);
        If(cond', thn', els')
      case Op(op, oe1, oe2) =>
        var oe1' := Eliminate(oe1);
        var oe2' := Eliminate(oe2);
        if op.Mul? && (IsZeroMulPure(oe1', oe2') || IsZeroMulPure(oe2', oe1')) then
          ZeroExpr
        else
          Op(op, oe1', oe2')
      case Seq(e1, e2) =>
        var e1' := Eliminate(e1);
        var e2' := Eliminate(e2);
        Seq(e1', e2')
  }

  predicate EqResult(res: InterpResult, res': InterpResult)
  {
    match (res, res')
      case (Success((v, ctx1)), Success((v', ctx1'))) =>
        && v == v'
        && ctx1' == ctx1
      case (Failure, _) =>
        true
      case _ =>
        false
  }

  //
  // Below, we prove that if we evaluate an expression starting from equivalent contexts,
  // then we evaluate to equivalent results.
  //

  // Rem.: we need an optional variable, otherwise we can't prove ``InductBind_Fail``.
  // The reason is that if there is variable shadowing we ignore the body of the let,
  // but the induction hypothesis takes as precondition that `x` doesn't appear in the
  // expression: we thus have to update the state to reflect the fact that we don't need
  // this condition on the body.

  type S = Context
  type V = int

  ghost const Zero: V := 0

  predicate P ...
  {
    var e' := Eliminate(e);
    var res := InterpExpr(e, st);
    var res' := InterpExpr(e', st);
    EqResult(res, res')
  }

  predicate P_Succ ...
  {
    var e' := Eliminate(e);
    var res := InterpExpr(e, st);
    var res' := InterpExpr(e', st);
    && EqResult(res, res')
    && res == Success((v, st'))
  }

  predicate P_Fail ...
  {
    var e' := Eliminate(e);
    var res := InterpExpr(e, st);
    var res' := InterpExpr(e', st);
    && EqResult(res, res')
    && res.Failure?
  }

  function AssignState ...
  {
    var ctx := st;
    var ctx1 := ctx[v := val];
    var st' := ctx1;
    st'
  }

  function BindStartScope ...
  {
    var ctx := st;
    var ctx1 := ctx[v := val];
    var st' := ctx1;
    st'
  }

  function BindEndScope ...
  {
    var ctx0 := st0;
    var ctx := st;
    var ctx1 := ctx0 + (ctx - {v});
    var st' := ctx1;
    st'
  }

  function P_Step ...
  {
    var Success((v, ctx1)) := InterpExpr(e, st);
    (ctx1, v)
  }

  lemma P_Fail_Sound ... {}
  lemma P_Succ_Sound ... {}
  lemma InductVar ... {}
  lemma InductLiteral ... {}
  lemma InductIf_Fail ... {}
  lemma InductIf_Succ ... {}

  lemma IsZeroMulPure_Implies_EvalsToZero(e1: Expr, e2: Expr, ctx: Context)
    requires IsZeroMulPure(e1, e2)
    ensures
      var res := InterpExpr(Op(Mul, e1, e2), ctx);
      res.Success? ==> res.value == (Zero, ctx)
  {
    Pure.InterpExpr_Pure(e2, ctx);
  }

  lemma IsZeroMulPure_Implies_EvalsToZero_Forall()
    ensures
      forall e1, e2, ctx | IsZeroMulPure(e1, e2) ::
      var res := InterpExpr(Op(Mul, e1, e2), ctx);
      res.Success? ==> res.value == (Zero, ctx)
  {
    forall e1, e2, ctx | IsZeroMulPure(e1, e2)
      ensures
      var res := InterpExpr(Op(Mul, e1, e2), ctx);
      res.Success? ==> res.value == (Zero, ctx)
    {
      IsZeroMulPure_Implies_EvalsToZero(e1, e2, ctx);
    }
  }

  lemma InductOp_Fail ... { IsZeroMulPure_Implies_EvalsToZero_Forall(); }
  
  lemma InductOp_Succ ... { IsZeroMulPure_Implies_EvalsToZero_Forall(); }
  lemma InductSeq_Fail ... {}
  lemma InductSeq_Succ ... {}
  lemma InductAssign_Fail ... {}

  lemma InductAssign_Succ ... {}

  lemma InductBind_Fail ... {}
  lemma InductBind_Succ ... {}

  lemma Eliminate_Eq(e: Expr, ctx: Context)
    ensures
      var e' := Eliminate(e);
      var res := InterpExpr(e, ctx);
      var res' := InterpExpr(e', ctx);
      EqResult(res, res')
    // The final theorem.
  {
    P_Satisfied(ctx, e);
  }
}

include "Utils.dfy"
include "AST.dfy"
include "Interp.dfy"

abstract module Induction {
  import opened Utils
  import opened AST

  // A state
  type S(!new)

  // A value
  type V(!new)

  ghost const Zero: V

  // ``P`` is the property of interest that we want to prove about the interpreter. It is often
  // possible to distinguish two cases in the proof: the case corresponding to a successful
  // execution of the interpreter, and the case corresponding to a failing execution. For instance,
  // let's say you want to prove that evaluating a pure expression leaves the state unchanged:
  // the property is trivially true in case the interpreter fails its execution. For this reason,
  // we decompose ``P`` into ``P_Fail`` (failed execution) and ``P_Succ`` (successful execution,
  // which also takes as inputs the state and value resulting from the execution).
  //
  // One important property to enforce is that:
  // `P(st, e) <==> P_Fail(st, e) || exists st', v :: P_Succ(st, e, st', v)`
  // This is enforced by: ``P_Fail_Sound``, ``P_Succ_Sound`` and ``P_Step``.
  predicate P(st: S, e: Expr)
  predicate P_Succ(st: S, e: Expr, st': S, v: V) // Success
  predicate P_Fail(st: S, e: Expr) // Failure

  // For the ``Assign`` case
  function AssignState(st: S, v: string, val: V): (st':S)

  // For the ``Bind`` case
  function BindStartScope(st: S, v: string, val: V): (st':S)

  // For ``Bind``: used to remove from the context the variables introduced by the bind, while
  // preserving the mutation. `st0` is the state just before we introduce the let-bounded variables,
  // `st1 is the state resulting from evaluating the body.
  function BindEndScope(st0: S, st: S, v: string): (st':S)

  function P_Step(st: S, e: Expr): (res: (S, V))
    requires P(st, e)
    requires !P_Fail(st, e)
    ensures P_Succ(st, e, res.0, res.1)

  lemma P_Fail_Sound(st: S, e: Expr)
    requires P_Fail(st, e)
    ensures P(st, e)

  lemma P_Succ_Sound(st: S, e: Expr, st': S, v: V)
    requires P_Succ(st, e, st', v)
    ensures P(st, e)

  lemma InductVar(st: S, e: Expr)
    requires e.Var?
    requires !P_Fail(st, e)
    ensures P(st, e)

  lemma InductLiteral(st: S, e: Expr)
    requires e.Literal?
    requires !P_Fail(st, e)
    ensures P(st, e)

  lemma InductIf_Fail(st: S, e: Expr, cond: Expr, thn: Expr, els: Expr)
    requires e.If? && e.cond == cond && e.thn == thn && e.els == els
    requires !P_Fail(st, e)
    requires P(st, cond)
    ensures !P_Fail(st, cond)

  lemma InductIf_Succ(st: S, e: Expr, cond: Expr, thn: Expr, els: Expr, st_cond: S, condv: V)
    requires e.If? && e.cond == cond && e.thn == thn && e.els == els
    requires !P_Fail(st, e)
    requires P_Succ(st, cond, st_cond, condv)
    requires P(st_cond, thn)
    requires P(st_cond, els)
    ensures P(st, e)

  lemma InductOp_Fail(st: S, e: Expr, op: BinOp, e1: Expr, e2: Expr)
    requires e.Op? && e.op == op && e.oe1 == e1 && e.oe2 == e2
    requires !P_Fail(st, e)
    ensures !P_Fail(st, e1)
    ensures forall st1, v1 | P_Succ(st, e1, st1, v1) :: !P_Fail(st1, e2)

  lemma InductOp_Succ(st: S, e: Expr, op: BinOp, e1: Expr, e2: Expr, st1: S, v1: V)
    requires e.Op? && e.op == op && e.oe1 == e1 && e.oe2 == e2
    requires !P_Fail(st, e)
    requires P_Succ(st, e1, st1, v1)
    requires P(st1, e2)
    ensures P(st, e)

  lemma InductSeq_Fail(st: S, e: Expr, e1: Expr, e2: Expr)
    requires e.Seq? && e.e1 == e1 && e.e2 == e2
    requires !P_Fail(st, e)
    ensures !P_Fail(st, e1)
    ensures forall st1, v1 | P_Succ(st, e1, st1, v1) :: !P_Fail(st1, e2)

  lemma InductSeq_Succ(st: S, e: Expr, e1: Expr, e2: Expr, st1: S, v1: V)
    requires e.Seq? && e.e1 == e1 && e.e2 == e2
    requires !P_Fail(st, e)
    requires P_Succ(st, e1, st1, v1)
    requires P(st1, e2)
    ensures P(st, e)

  lemma InductAssign_Fail(st: S, e: Expr, avar: string, aval: Expr)
    requires e.Assign? && e.avar == avar && e.aval == aval
    requires !P_Fail(st, e)
    requires P(st, aval)
    ensures !P_Fail(st, aval)

  lemma InductAssign_Succ(
    st: S, e: Expr, avar: string, aval: Expr, st1: S, value: V, st2: S)
    requires e.Assign? && e.avar == avar && e.aval == aval
    requires !P_Fail(st, e)
    requires P_Succ(st, aval, st1, value)
    requires st2 == AssignState(st1, avar, value)
    // This post is not necessary: what matters is that ``AssignState`` appears somewhere,
    // but it may help Z3.
    ensures P_Succ(st, e, st2, Zero)
    ensures P(st, e)

  lemma InductBind_Fail(st: S, e: Expr, bvar: string, bval: Expr, body: Expr)
    requires e.Bind? && e.bvar == bvar && e.bval == bval && e.body == body
    requires !P_Fail(st, e)
    requires P(st, bval)
    ensures !P_Fail(st, bval)
    ensures
      forall st1, val | P_Succ(st, bval, st1, val) ::
      && !P_Fail(BindStartScope(st1, bvar, val), body)

  lemma InductBind_Succ(
    st: S, e: Expr, bvar: string, bval: Expr, body: Expr,
    st1: S, bvarv: V, st2: S, st3: S, v: V, st4: S)
    requires e.Bind? && e.bvar == bvar && e.bval == bval && e.body == body
    requires !P_Fail(st, e)
    requires P_Succ(st, bval, st1, bvarv)
    requires st2 == BindStartScope(st1, bvar, bvarv)
    requires P_Succ(st2, body, st3, v)
    requires st4 == BindEndScope(st1, st3, bvar) // ``StateBindEndScope`` may have a postcondition, so it's good to have it
    ensures P_Succ(st, e, st4, v)

  //
  // Lemmas
  //

  lemma P_Satisfied(st: S, e: Expr)
    ensures P(st, e)
    decreases e, 1
  {
    if P_Fail(st, e) {
      P_Fail_Sound(st, e);
    }
    else {
      P_Satisfied_Succ(st, e);
    }
  }

  lemma P_Satisfied_Succ(st: S, e: Expr)
    requires !P_Fail(st, e)
    ensures P(st, e)
    decreases e, 0
  {
    match e {
      case Var(_) =>
        InductVar(st, e);

      case Literal(_) =>
        InductLiteral(st, e);

      case Op(op, e1, e2) =>
        // Recursion
        P_Satisfied(st, e1);

        assert !P_Fail(st, e1) by { InductOp_Fail(st, e, op, e1, e2); }
        var (st1, v1) := P_Step(st, e1);

        // Recursion
        P_Satisfied(st1, e2);

        assert !P_Fail(st1, e2) by { InductOp_Fail(st, e, op, e1, e2); }
        var (st2, v2) := P_Step(st1, e2);

        InductOp_Succ(st, e, op, e1, e2, st1, v1);

      case Seq(e1, e2) =>
        // Recursion
        P_Satisfied(st, e1);

        assert !P_Fail(st, e1) by { InductSeq_Fail(st, e, e1, e2); }
        var (st1, v1) := P_Step(st, e1);

        // Recursion
        P_Satisfied(st1, e2);

        assert !P_Fail(st1, e2) by { InductSeq_Fail(st, e, e1, e2); }
        var (st2, v2) := P_Step(st1, e2);

        InductSeq_Succ(st, e, e1, e2, st1, v1);

      case If(cond, thn, els) =>
        // Recursion
        P_Satisfied(st, cond);

        // Evaluate the condition
        InductIf_Fail(st, e, cond, thn, els);
        assert !P_Fail(st, cond);
        var (st_cond, condv) := P_Step(st, cond);

        P_Satisfied(st_cond, thn); // Recursion
        P_Satisfied(st_cond, els); // Recursion

        InductIf_Succ(st, e, cond, thn, els, st_cond, condv);

      case Assign(avar, aval) =>
        // Recursion
        P_Satisfied(st, aval);

        assert !P_Fail(st, aval) by { InductAssign_Fail(st, e, avar, aval); }
        var (st1, value) := P_Step(st, aval);

        var st2 := AssignState(st1, avar, value);
        InductAssign_Succ(st, e, avar, aval, st1, value, st2);

      case Bind(bvar, bval, body) =>

        P_Satisfied(st, bval); // Recursion
        assert !P_Fail(st, bval) by { InductBind_Fail(st, e, bvar, bval, body); }
        var (st1, bvarv) := P_Step(st, bval);

        var st2 := BindStartScope(st1, bvar, bvarv);
        P_Satisfied(st2, body); // Recursion
        assert !P_Fail(st2, body) by { InductBind_Fail(st, e, bvar, bval, body); }

        var (st3, v) := P_Step(st2, body);
        var st4 := BindEndScope(st1, st3, bvar);

        InductBind_Succ(st, e, bvar, bval, body, st1, bvarv, st2, st3, v, st4);
        P_Succ_Sound(st, e, st4, v);
    }
  }
}

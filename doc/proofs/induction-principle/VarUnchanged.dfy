include "Utils.dfy"
include "AST.dfy"
include "Interp.dfy"
include "Induction.dfy"

module VarUnchanged refines Induction {
  // We write a small analysis which checks if a variable appears in an assignment in
  // an expression (we take into account shadowing introduced by let-bindings), and prove
  // that if it is not the case, then evaluating the expression leaves the variable
  // unchanged.

  import opened Interp

  predicate method VarUnchanged(x: string, e: Expr)
    // Returns true if no assignments of `x` (not shadowed by a let-binding) appears
    // in `e`.
  {
    match e
      case Var(name) => false
      case Literal(n) => false
      case Bind(bvar, bval, body) =>
        // The rhs doesn't update x
        VarUnchanged(x, bval) &&
        // If the binding doesn't shadow x, the body of the let-binding doesn't update x
        (bvar == x || VarUnchanged(x, body))
      case Assign(avar, aval) =>
        avar != x && VarUnchanged(x, aval)
      case If(cond, thn, els) =>
        VarUnchanged(x, cond) && VarUnchanged(x, thn) && VarUnchanged(x, els)
      case Op(op, oe1, oe2) =>
        VarUnchanged(x, oe1) && VarUnchanged(x, oe2)
      case Seq(e1, e2) =>
        VarUnchanged(x, e1) && VarUnchanged(x, e2)
  }

  predicate ResultSameX(st: S, res: InterpResult)
  {
    match res
      case Success((v, ctx)) =>
        st.x.Some? ==>
        && st.x.value in ctx.Keys
        && st.ctx[st.x.value] == ctx[st.x.value]
      case Failure =>
        true
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
  datatype MState = MState(x: Option<string>, ctx: Context)
  
  type S = st:MState | st.x.Some? ==> st.x.value in st.ctx.Keys
    witness MState(None, map [])
  type V = int

  ghost const Zero: V := 0

  predicate Pre(st: S, e: Expr)
  {
    st.x.Some? ==> VarUnchanged(st.x.value, e)
  }

  predicate P ...
  {
    var res := InterpExpr(e, st.ctx);
    Pre(st, e) ==> ResultSameX(st, res)
  }

  predicate P_Succ ...
  {
    var res := InterpExpr(e, st.ctx);
    && Pre(st, e)
    && ResultSameX(st, res)
    && res == Success((v, st'.ctx))
    && st'.x == st.x
  }

  predicate P_Fail ...
  {
    var res := InterpExpr(e, st.ctx);
    Pre(st, e) ==> res.Failure?
  }

  function AssignState ...
  {
    var MState(x, ctx) := st;
    var ctx1 := ctx[v := val];
    var st' := MState(x, ctx1);
    st'
  }

  function BindStartScope ...
  {
    var MState(x, ctx) := st;
    var x' := if x.Some? && x.value == v then None else x;
    var ctx1 := ctx[v := val];
    var st' := MState(x', ctx1);
    st'
  }

  function BindEndScope ...
  {
    var MState(x0, ctx0) := st0;
    var MState(x, ctx) := st;
    var ctx1 := ctx0 + (ctx - {v});
    var st' := MState(x0, ctx1);
    st'
  }

  function P_Step ...
  {
    var Success((v, ctx1)) := InterpExpr(e, st.ctx);
    (MState(st.x, ctx1), v)
  }

  lemma P_Fail_Sound ... {}
  lemma P_Succ_Sound ... {}
  lemma InductVar ... {}
  lemma InductLiteral ... {}
  lemma InductIf_Fail ... {}
  lemma InductIf_Succ ... {}
  lemma InductOp_Fail ... {}
  lemma InductOp_Succ ... {}
  lemma InductSeq_Fail ... {}
  lemma InductSeq_Succ ... {}
  lemma InductAssign_Fail ... {}
  lemma InductAssign_Succ ... {}
  lemma InductBind_Fail ... {}
  lemma InductBind_Succ ... {}
}


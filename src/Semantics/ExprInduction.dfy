include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "Interp.dfy"
include "Equiv.dfy"

abstract module Bootstrap.Semantics.ExprInduction {
  // The following abstract module defines a functor to factorize the proofs about the interpreter.
  // It works as follows.
  //
  // Writing any proof about the interpreter (for instance, that evaluating a pure expression leaves
  // the state unchanged, or that evaluating the same expression from two different "equivalent" states
  // leads to equivalent results) is very tedious because we need to copy-paste a lot of code. Moreover,
  // most of the proof is often boring, though error-prone because it is easy to, say, not write
  // the calls to the induction hypothesis with the proper arguments (and we are blind while doing
  // the proofs...). However, given the proper hypotheses, most of those proofs should go through
  // pretty easily.
  //
  // For instance, let's say you want to prove the property `forall e. P(e)` where
  // `P(e) := forall ctx, ctx'. ctx ~= ctx' ==> Interp(e, ctx) ~= Interp(e, ctx')` (for some notion
  // of equivalence). The proof is of course made by induction, and cases like `if b then thn else els`
  // should be trivial: all you need to do is call the induction hypothesis on `b`, `thn` and `els`,
  // and the proof should go through automatically. However, you still need to do it, which consumes
  // time, takes a lot of lines of code, and can be error-prone.
  // 
  // The "induction functor" is an attempt at factorizing those proofs, by providing an interface
  // which is roughly structured as follows:
  // ```
  // abstract module ExprInduction {
  //   // Property of interest, to be defined by the user
  //   predicate P(e: Expr)
  //
  //   // Set of lemmas needed to prove one case in an induction step, and to be proven by the user.
  //   // Those lemmas are written so that the induction hypotheses necessary to perform the proofs
  //   // are given as preconditions:
  //   lemma InductIf(e: Expr)
  //     requires e.If?
  //     requires P(e.cond) // Induction hypothesis
  //     requires P(e.thn)  // Induction hypothesis
  //     requires P(e.els)  // Induction hypothesis
  //     ensures P(e)
  //
  //   ... // Other lemmas for the remaining cases of the AST
  //
  //   // The proof of induction, performed once and for all
  //   lemma P_Satisfied(e: Expr)
  //     ensures P(e)
  //   {
  //     ... // Match on the expression, call the proper "Induct..." lemmas, etc.
  //   }
  // }
  // ```
  //
  // An instantiation of the "induction functor" would look like this:
  // ```
  // module EqInterpRefl refines ExprInduction {
  //   // Define the property of interest
  //   predicate P(e: Expr) {
  //     forall env, ctx, ctx' ::
  //     EqState(ctx, ctx') ==> EqInterpResultValue(Interp(e, env, ctx), Interp(e, env, ctx'))
  //   }
  //
  //   // Prove the induction lemmas.
  //   // Many of those lemmas should go through automatically! Remember: in the `if then else" case,
  //   // we just need the induction hypothesis to be applied on the condition and the branches, and
  //   // this is given by the lemma preconditions.
  //   lemma InductIf ... {}
  //
  //   ... // Other lemmas
  //
  //   // And we get `forall e. P(e)` from `P_Satisfied`, whose proof is given for free by the functor.
  // }
  // ```
  //
  // If you want to see a simple instantiation example in which most proofs go through automatically,
  // see `InterpStateIneq`. If you want to see a more complex example, see `EqInterpScopes`.
  //
  // Rem.: the predicate `P` doesn't have the same signature in the real functor, but the idea is similar.

  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import opened Interp
  import opened Values
  import opened Equiv
  import opened Utils.Lib.Datatypes

  type Expr = Interp.Expr

  //
  // Declarations
  //

  // A state
  type S(!new)

  // A value
  type V(!new)

  // A sequence of values
  type VS(!new)

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

  // ``Pes`` is the property of interest over sequences of expressions.
  predicate Pes(st: S, es: seq<Expr>)
  predicate Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS) // Success
  predicate Pes_Fail(st: S, es: seq<Expr>) // Failure
    
  function AppendValue(v: V, vs: VS): VS // Returns: [v] + vs
  function SeqVToVS(vs: seq<V>): VS

  predicate VS_UpdateStatePre(st: S, vars: seq<string>, argvs: VS)

  // For the ``Abs`` case: builds the closure state from the current state
  function BuildClosureCallState(st: S, vars: seq<string>, body: Expr, env: Environment, argvs: VS): (st':S)
    requires VS_UpdateStatePre(st, vars, argvs)

  // For the ``Update`` and the ``Bind`` case: returns a new state updated with new bindings.
  function UpdateState(st: S, vars: seq<string>, vals: VS): (st':S)
    requires VS_UpdateStatePre(st, vars, vals)

  // Rollback
  function StateSaveToRollback(st: S, vars: seq<string>): (st':S)

  // For ``Bind``: used to remove from the context the variables introduced by the bind, while
  // preserving the mutation. `st0` is the state just before we introduce the let-bounded variables,
  // `st1 is the state resulting from evaluating the body.
  function StateBindEndScope(st0: S, st: S, vars: seq<string>): (st':S)

  function StateStartScope(st: S): (st':S)
  function StateEndScope(st0: S, st: S): (st':S)

  // DISCUSS: can't write the postcondition on ``NilVS``, hence this auxiliary function
  function GetNilVS(): (vs:VS)
    ensures vs == SeqVToVS([])

  // Empty sequence of values
  ghost const NilVS:VS := GetNilVS()
  ghost const UnitV:V

  function VS_Last(vs: VS): V
    requires vs != NilVS

  function P_Step(st: S, e: Expr): (res: (S, V))
    requires P(st, e)
    requires !P_Fail(st, e)
    ensures P_Succ(st, e, res.0, res.1)

  function P_StepState(st: S, e: Expr): S
    requires P(st, e)
    requires !P_Fail(st, e)
  {
    P_Step(st, e).0
  }

  function P_StepValue(st: S, e: Expr): V
    requires P(st, e)
    requires !P_Fail(st, e)
  {
    P_Step(st, e).1
  }

  function Pes_Step(st: S, es: seq<Expr>): (res: (S, VS))
    requires Pes(st, es)
    requires !Pes_Fail(st, es)
    ensures Pes_Succ(st, es, res.0, res.1)

  function Pes_StepState(st: S, es: seq<Expr>): S
    requires Pes(st, es)
    requires !Pes_Fail(st, es)
  {
    Pes_Step(st, es).0
  }

  function Pes_StepValue(st: S, es: seq<Expr>): VS
    requires Pes(st, es)
    requires !Pes_Fail(st, es)
  {
    Pes_Step(st, es).1
  }

  lemma P_Fail_Sound(st: S, e: Expr)
    requires P_Fail(st, e)
    ensures P(st, e)

  lemma P_Succ_Sound(st: S, e: Expr, st': S, v: V)
    requires P_Succ(st, e, st', v)
    ensures P(st, e)

  lemma Pes_Fail_Sound(st: S, es: seq<Expr>)
    requires Pes_Fail(st, es)
    ensures Pes(st, es)

  lemma Pes_Succ_Sound(st: S, es: seq<Expr>, st': S, vs: VS)
    requires Pes_Succ(st, es, st', vs)
    ensures Pes(st, es)

  lemma Pes_Succ_Inj(st: S, es: seq<Expr>, st1: S, st1': S, vs: VS, vs': VS)
    requires Pes_Succ(st, es, st1, vs)
    requires Pes_Succ(st, es, st1', vs')
    ensures st1 == st1'
    ensures vs == vs'

  lemma SeqVToVS_Append(v: V, vs: seq<V>)
    ensures AppendValue(v, SeqVToVS(vs)) == SeqVToVS([v] + vs)

  lemma InductVar(st: S, e: Expr)
    requires e.Var?
    requires !P_Fail(st, e)
    ensures P(st, e)

  lemma InductLiteral(st: S, e: Expr)
    requires e.Literal?
    ensures P(st, e)

  lemma InductAbs(st: S, e: Expr, vars: seq<string>, body: Expr)
    requires e.Abs? && e.vars == vars && e.body == body
    requires !P_Fail(st, e)
    requires forall env, argvs | VS_UpdateStatePre(st, vars, argvs) :: P(BuildClosureCallState(st, vars, body, env, argvs), body)
    ensures P(st, e)

  lemma InductAbs_CallState(st: S, e: Expr, vars: seq<string>, body: Expr, env: Environment, argvs: VS, st_ret: S, retv: V)
    requires e.Abs? && e.vars == vars && e.body == body
    requires VS_UpdateStatePre(st, vars, argvs)
    requires !P_Fail(st, e)
    requires P_Succ(BuildClosureCallState(st, vars, body, env, argvs), body, st_ret, retv)
    ensures P(BuildClosureCallState(st, vars, body, env, argvs), body)

  lemma InductExprs_Nil(st: S)
    ensures !Pes_Fail(st, []) ==> Pes_Succ(st, [], st, NilVS) // Pes_Fail: because, for instance, the state may not satisfy the proper invariant

  // TODO(SMH): I grouped everything (success and failure case) in this lemma. Maybe do the same for some others?
  // For instance, it might be worth doing it for the "trivial" cases, which should never require work from the
  // user side (ex.: `if then else`).
  lemma InductExprs_Cons(st: S, e: Expr, es: seq<Expr>)
    ensures P_Fail(st, e) ==> Pes_Fail(st, [e] + es)
    ensures !P_Fail(st, e) ==> forall st1, v :: P_Succ(st, e, st1, v) && Pes_Fail(st1, es) ==> Pes_Fail(st, [e] + es)
    ensures forall st1, v, st2, vs :: P_Succ(st, e, st1, v) && Pes_Succ(st1, es, st2, vs) ==> Pes_Succ(st, [e] + es, st2, AppendValue(v, vs))

  lemma InductApplyLazy_Fail(st: S, e: Expr, arg0: Expr, arg1: Expr)
    requires e.Apply? && e.aop.Lazy? && e.args == [arg0, arg1]
    requires !P_Fail(st, e)
    // TODO(SMH): requires P(st, arg0)
    ensures !P_Fail(st, arg0)

  lemma InductApplyLazy_Succ(st: S, e: Expr, arg0: Expr, arg1: Expr, st1: S, v0: V)
    requires e.Apply? && e.aop.Lazy? && e.args == [arg0, arg1]
    requires !P_Fail(st, e)
    requires P_Succ(st, arg0, st1, v0)
    requires P(st1, arg1) // We can only assume that we successfully evaluated the first argument (not the second one), because the operator is lazy
    ensures P(st, e)

  lemma InductApplyEager_Fail(st: S, e: Expr, args: seq<Expr>)
    requires e.Apply? && e.aop.Eager? && e.args == args
    requires !P_Fail(st, e)
    // TODO(SMH): requires Pes(st, args)
    ensures !Pes_Fail(st, args)

  lemma InductApplyEagerUnaryOp_Succ(st: S, e: Expr, op: UnaryOps.T, arg0: Expr, st1: S, v0: V)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.UnaryOp? && e.aop.eOp.uop == op && e.args == [arg0]
    requires !P_Fail(st, e)
    requires P_Succ(st, arg0, st1, v0)
    requires Pes(st, [arg0])
    requires !Pes_Fail(st, [arg0])
    requires Pes_Step(st, [arg0]) == (st1, SeqVToVS([v0]))
    ensures P(st, e)

  lemma InductApplyEagerBinaryOp_Succ(st: S, e: Expr, op: BinaryOps.T, arg0: Expr, arg1: Expr, st1: S, v0: V, st2: S, v1: V)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.BinaryOp? && e.aop.eOp.bop == op && e.args == [arg0, arg1]
    requires !P_Fail(st, e)
    requires P_Succ(st, arg0, st1, v0)
    requires P_Succ(st1, arg1, st2, v1)
    requires Pes(st, [arg0, arg1])
    requires !Pes_Fail(st, [arg0, arg1])
    requires Pes_Step(st, [arg0, arg1]) == (st2, SeqVToVS([v0, v1]))
    ensures P(st, e)

  lemma InductApplyEagerTernaryOp_Succ(
    st: S, e: Expr, op: TernaryOps.T, arg0: Expr, arg1: Expr, arg2: Expr, st1: S, v0: V, st2: S, v1: V, st3: S, v2: V)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.TernaryOp? && e.aop.eOp.top == op && e.args == [arg0, arg1, arg2]
    requires !P_Fail(st, e)
    requires P_Succ(st, arg0, st1, v0)
    requires P_Succ(st1, arg1, st2, v1)
    requires P_Succ(st2, arg2, st3, v2)
    requires Pes(st, [arg0, arg1, arg2])
    requires !Pes_Fail(st, [arg0, arg1, arg2])
    requires Pes_Step(st, [arg0, arg1, arg2]) == (st3, SeqVToVS([v0, v1, v2]))
    ensures P(st, e)

  lemma InductApplyEagerBuiltinDisplay(st: S, e: Expr, ty: Types.Type, args: seq<Expr>, st1: S, argvs: VS)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.Builtin? && e.aop.eOp.builtin.Display? && e.aop.eOp.builtin.ty == ty && e.args == args
    requires !P_Fail(st, e)
    requires Pes_Succ(st, args, st1, argvs)
    ensures P(st, e)

  lemma InductApplyEagerFunctionCall(st: S, e: Expr, f: Expr, args: seq<Expr>, st1: S, fv: V, st2: S, argvs: VS)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.FunctionCall? && e.args == [f] + args
    requires !P_Fail(st, e)
    requires P_Succ(st, f, st1, fv)
    requires Pes_Succ(st1, args, st2, argvs)
    requires Pes(st, [f] + args)
    requires !Pes_Fail(st, [f] + args)
    requires Pes_StepValue(st, [f] + args) == AppendValue(fv, argvs)
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

  // STYLE: In the lemma below, we don't need to take `st1` (nor `vars`) as input (because we enforce it is equal
  // to `StateSaveToRollback(st, vars)` in the precondition). We adopt this style because it
  // allows to not duplicate code in the postconditions (say, if `st1` appears in several `ensures`)
  // and to easily access `st1` when debugging the proofs in the instantiations of the induction
  // functor (the user doesn't need to introduce `var st1 := StateSaveToRollback(st, vars)`);
  // This requires slightly more work in the inductive proof of `P_Satisfied`, but is totally
  // bearable. We adopt this style in the other lemma statements.
  // DISCUSS: ok with this style?
  lemma InductVarDecl_None_Succ(st: S, e: Expr, vdecls: seq<Exprs.TypedVar>, vars: seq<string>, st1: S)
    requires e.VarDecl? && e.vdecls == vdecls && e.ovals.None?
    requires !P_Fail(st, e)
    requires vars == VarsToNames(vdecls)
    requires st1 == StateSaveToRollback(st, vars)
    // This is not necessary but can help the proofs - what really matters is that ``StateSaveToRollback`` appears somewhere
    ensures P_Succ(st, e, st1, UnitV)
    ensures P(st, e)

  lemma InductVarDecl_Some_Fail(st: S, e: Expr, vdecls: seq<Exprs.TypedVar>, vals: seq<Expr>)
    requires e.VarDecl? && e.vdecls == vdecls && e.ovals.Some? && e.ovals.value == vals
    requires !P_Fail(st, e)
    requires Pes(st, vals)
    ensures !Pes_Fail(st, vals)

  // DISCUSS: we want to consistently adopt the style we described for ``InductVarDecl_None_Succ``,
  // but this can be tricky in case a function like ``UpdateState`` takes a precondition. If this
  // lemma seems too convoluted, we could try to get rid of the precondition for ``UpdateState``
  // (but doesn't seem that easy nor natural to do), or we could not take `st3` as input.
  lemma InductVarDecl_Some_Succ(
      st: S, e: Expr, vdecls: seq<Exprs.TypedVar>, vars: seq<string>, vals: seq<Expr>, st1: S, values: VS, st2: S, st3: S)
    requires e.VarDecl? && e.vdecls == vdecls && e.ovals.Some? && e.ovals.value == vals
    requires !P_Fail(st, e)
    requires Pes_Succ(st, vals, st1, values)
    requires vars == VarsToNames(vdecls)
    requires st2 == StateSaveToRollback(st1, vars)
    // TODO(SMH): the VS_UpdateStatePre could be given by InductVarDecl_Some_Fail
    requires VS_UpdateStatePre(st2, vars, values) ==> st3 == UpdateState(st2, vars, values) // Slightly convoluted, but ``UpdateState`` has a pre
    ensures VS_UpdateStatePre(st2, vars, values)
    // This is not necessary but can help the proofs - what really matters is that ``StateSaveToRollback``
    // and ``UpdateState`` appear somewhere
    ensures P_Succ(st, e, st3, UnitV) // TODO: remove: it is not true in the case of variables inlining. Maybe: P_Succ(...) ==> P(...) (trivially true, but can help Z3)?
    ensures P(st, e)

  lemma InductUpdate_Fail(st: S, e: Expr, vars: seq<string>, vals: seq<Expr>)
    requires e.Update? && e.vars == vars && e.vals == vals
    requires !P_Fail(st, e)
    requires Pes(st, vals)
    ensures !Pes_Fail(st, vals)

  lemma InductUpdate_Succ(
    st: S, e: Expr, vars: seq<string>, vals: seq<Expr>, st1: S, values: VS, st2: S)
    requires e.Update? && e.vars == vars && e.vals == vals
    requires !P_Fail(st, e)
    requires Pes_Succ(st, vals, st1, values)
    // TODO(SMH): the VS_UpdateStatePre could be given by InductUpdateFail
    requires VS_UpdateStatePre(st1, vars, values) ==> st2 == UpdateState(st1, vars, values) // Slightly convoluted, but ``UpdateState`` has a pre
    ensures VS_UpdateStatePre(st1, vars, values)
    // This post is not necessary: what matters is that ``UpdateState`` appears somewhere
    ensures P_Succ(st, e, st2, UnitV)
    ensures P(st, e)

  lemma InductBind_Fail(st: S, e: Expr, bvars: seq<Exprs.TypedVar>, bvals: seq<Expr>, bbody: Expr, vars: seq<string>)
    requires e.Bind? && e.bvars == bvars && e.bvals == bvals && e.bbody == bbody
    requires !P_Fail(st, e)
    requires vars == VarsToNames(bvars)
    requires Pes(st, bvals)
    ensures !Pes_Fail(st, bvals)
    ensures
      forall st1, vals :: Pes_Succ(st, bvals, st1, vals) ==>
      && VS_UpdateStatePre(st1, vars, vals)
      && !P_Fail(UpdateState(st1, vars, vals), bbody)

  lemma InductBind_Succ(
    st: S, e: Expr, bvars: seq<Exprs.TypedVar>, bvals: seq<Expr>, bbody: Expr, vars: seq<string>,
    st1: S, vals: VS, st2: S, st3: S, v: V, st4: S)
    requires e.Bind? && e.bvars == bvars && e.bvals == bvals && e.bbody == bbody
    requires !P_Fail(st, e)
    requires vars == VarsToNames(bvars)
    requires Pes_Succ(st, bvals, st1, vals)
    requires VS_UpdateStatePre(st1, vars, vals)
    requires st2 == UpdateState(st1, vars, vals)
    requires P_Succ(st2, bbody, st3, v)
    requires st4 == StateBindEndScope(st1, st3, vars) // ``StateBindEndScope`` may have a postcondition, so it's good to have it
    // We don't necessarily have P_Succ(...) (can happen when we verify transformations: one of the
    // intermediate states may not be equal to what we have above, but `P(st,e)` is still true), so
    // we simply write an implication to guide the solver.
    ensures P_Succ(st, e, st4, v) ==> P(st, e)
    ensures P(st, e)

  lemma InductBlock_Fail(st: S, e: Expr, stmts: seq<Expr>, st_start: S)
    requires e.Block? && e.stmts == stmts
    requires !P_Fail(st, e)
    requires st_start == StateStartScope(st)
    requires Pes(st_start, stmts)
    ensures !Pes_Fail(st_start, stmts)

  // DISCUSS: we can't have this automatic proofs for this lemma, because we implicitly rely on the
  // fact that ``InterpBlock_Exprs`` behaves like ``InterpExprs``, which requires a call to lemma
  // ``InterpExprs_Block_Equiv_Strong`` (see the induction functor instantiation in
  // ``InterpBlock_Exprs_StateSmaller`` for instance - also note that ``InterpExprs_Block_Equiv_Strong``
  // has some issues, see the comments there).
  // There are two ways of avoiding that:
  // - rewrite ``InterpBlock`` in terms of ``InterpExprs`` (see the discussion for ``InterpBlock``)
  // - add more lemmas and predicates in the induction functors, for the specific case of ``InterpBlock_Exprs``
  //   (this seems cumbersome)
  lemma InductBlock_Succ(st: S, e: Expr, stmts: seq<Expr>, st_start: S, st_stmts: S, vs: VS, st_end: S, vf: V)
    requires e.Block? && e.stmts == stmts
    requires !P_Fail(st, e)
    requires st_start == StateStartScope(st)
    requires Pes_Succ(st_start, stmts, st_stmts, vs)
    requires vf == if vs == NilVS then UnitV else VS_Last(vs) // TODO(SMH): I'm not super fan of that
    requires st_end == StateEndScope(st, st_stmts)
    ensures P_Succ(st, e, st_end, vf)


  //
  // Lemmas
  //

  lemma P_Satisfied(st: S, e: Expr)
    ensures P(st, e)
    decreases e.Size(), 1
  {
    if P_Fail(st, e) {
      P_Fail_Sound(st, e);
    }
    else {
      P_Satisfied_Succ(st, e);
    }
  }

  function InductExprs_Step(st: S, e: Expr, es: seq<Expr>): (out: (S, V, S, VS))
    requires !Pes_Fail(st, [e] + es)
    ensures
      var (st1, v, st2, vs) := out;
      && P_Succ(st, e, st1, v)
      && Pes_Succ(st1, es, st2, vs)
      && !Pes_Fail(st1, es)
    ensures Pes(st, [e] + es)
    ensures
      var (stf, vsf) := Pes_Step(st, [e] + es);
      var (st1, v, st2, vs) := out;
      stf == st2 && vsf == AppendValue(v, vs)
    decreases Exprs.Exprs_Size([e] + es), 4
  {
    Pes_Satisfied(st, [e] + es);
    
    P_Satisfied(st, e); // Recursion
    assert !P_Fail(st, e) ==> Pes(P_StepState(st, e), es) by {
      if !P_Fail(st, e) {
        Pes_Satisfied(P_StepState(st, e), es); // Recursion
      }
    }

    InductExprs_Cons(st, e, es);

    var (st1, v) := P_Step(st, e);
    var (st2, vs) := Pes_Step(st1, es);

    var (stf, vsf) := Pes_Step(st, [e] + es);
    Pes_Succ_Inj(st, [e] + es, st2, stf, AppendValue(v, vs), vsf);

    (st1, v, st2, vs)
  }

  lemma P_Satisfied_Succ(st: S, e: Expr)
    requires !P_Fail(st, e)
    ensures P(st, e)
    decreases e.Size(), 0
  {
    reveal SupportsInterp();
    
    match e {
      case Var(_) =>
        InductVar(st, e);

      case Literal(_) =>
        InductLiteral(st, e);

      case Abs(vars, body) =>
        forall env, argvs | VS_UpdateStatePre(st, vars, argvs)
          ensures P(BuildClosureCallState(st, vars, body, env, argvs), body) {
          var st_call := BuildClosureCallState(st, vars, body, env, argvs);
          if P_Fail(st_call, body) {
            P_Fail_Sound(st_call, body);
          }
          else {
            P_Satisfied(st_call, body); // Recursion
            var (st_ret, retv) := P_Step(st_call, body);
            InductAbs_CallState(st, e, vars, body, env, argvs, st_ret, retv);
          }
        }
        InductAbs(st, e, vars, body);

      case Apply(Lazy(_), _) =>
        var arg0 := e.args[0];
        var arg1 := e.args[1];
        P_Satisfied(st, arg0); // Recursion

        InductApplyLazy_Fail(st, e, arg0, arg1);
        assert !P_Fail(st, arg0);

        var (st1, v0) := P_Step(st, arg0);
        P_Satisfied(st1, arg1); // Recursion
        InductApplyLazy_Succ(st, e, arg0, arg1, st1, v0);

      case Apply(Eager(aop), _) =>
        Pes_Satisfied(st, e.args); // Recursion

        InductApplyEager_Fail(st, e, e.args);
        assert !Pes_Fail(st, e.args);

        var (st', vs) := Pes_Step(st, e.args);

        match aop {
          case UnaryOp(op) =>
            var arg0 := e.args[0];
            assert e.args == [arg0] + [];
            var (st1, v0, st2, vs1) := InductExprs_Step(st, arg0, []);

            // Prove that the sequence of arguments evaluates to: (st', [v0])
            var es := [];
            assert Pes_Succ(st1, es, st2, vs1);
            assert st2 == st';
            assert AppendValue(v0, vs1) == vs;
            InductExprs_Nil(st1);
            assert Pes_Succ(st1, es, st1, NilVS);
            Pes_Succ_Inj(st1, es, st1, st2, NilVS, vs1);
            SeqVToVS_Append(v0, []);
            assert [v0] + [] == [v0];
            assert SeqVToVS([v0]) == AppendValue(v0, NilVS);
            InductApplyEagerUnaryOp_Succ(st, e, op, arg0, st1, v0);

          case BinaryOp(op) =>
            var arg0 := e.args[0];
            var arg1 := e.args[1];
            assert e.args == [arg0, arg1];

            assert e.args == [arg0] + [arg1];
            var (st1, v0, st2, vs') := InductExprs_Step(st, arg0, [arg1]);

            assert [arg1] == [arg1] + [];
            var (st2', v1, st3, vs'') := InductExprs_Step(st1, arg1, []);

            // Prove that the sequence of arguments evaluates to: (st', [v0, v1])
            var es := [];
            InductExprs_Nil(st2');
            assert Pes_Succ(st2', es, st2', NilVS);
            Pes_Succ_Inj(st2', es, st2', st3, NilVS, vs'');
            SeqVToVS_Append(v1, []);
            SeqVToVS_Append(v0, [v1]);
            assert [v1] + [] == [v1];
            assert [v0] + [v1] == [v0, v1];
            assert SeqVToVS([v0, v1]) == AppendValue(v0, AppendValue(v1, NilVS));

            InductApplyEagerBinaryOp_Succ(st, e, op, arg0, arg1, st1, v0, st2', v1);

          case TernaryOp(op) =>
            var arg0 := e.args[0];
            var arg1 := e.args[1];
            var arg2 := e.args[2];
            assert e.args == [arg0, arg1, arg2];

            assert e.args == [arg0] + [arg1, arg2];
            var (st1, v0, st2, vs') := InductExprs_Step(st, arg0, [arg1, arg2]);

            assert [arg1, arg2] == [arg1] + [arg2];
            var (st2', v1, st3, vs'') := InductExprs_Step(st1, arg1, [arg2]);

            assert [arg2] == [arg2] + [];
            var (st3', v2, st4, vs''') := InductExprs_Step(st2', arg2, []);

            // Prove that the sequence of arguments evaluates to: (st', [v0, v1])
            var es := [];
            InductExprs_Nil(st3');
            assert Pes_Succ(st3', es, st3', NilVS);
            Pes_Succ_Inj(st3', es, st3', st4, NilVS, vs''');
            SeqVToVS_Append(v2, []);
            SeqVToVS_Append(v1, [v2]);
            SeqVToVS_Append(v0, [v1, v2]);
            assert [v2] + [] == [v2];
            assert [v1] + [v2] == [v1, v2];
            assert [v0] + [v1, v2] == [v0, v1, v2];
            assert SeqVToVS([v0, v1, v2]) == AppendValue(v0, AppendValue(v1, AppendValue(v2, NilVS)));

            InductApplyEagerTernaryOp_Succ(st, e, op, arg0, arg1, arg2, st1, v0, st2', v1, st3', v2);

          case Builtin(Display(ty)) =>
            var (st1, argvs) := Pes_Step(st, e.args);

            InductApplyEagerBuiltinDisplay(st, e, ty, e.args, st1, argvs);

          case Builtin(Print) =>
            assert false; // Unreachable for now

          case FunctionCall =>
            var f := e.args[0];
            var args := e.args[1..];

            assert e.args == [f] + args;
            var (st1, fv, st2, argvs) := InductExprs_Step(st, f, args);

            InductApplyEagerFunctionCall(st, e, f, args, st1, fv, st2, argvs);
        }

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

      case VarDecl(vdecls, ovals) =>        
        var vars := VarsToNames(vdecls);

        if ovals.Some? {
          Pes_Satisfied(st, ovals.value); // Recursion

          InductVarDecl_Some_Fail(st, e, vdecls, ovals.value);
          assert !Pes_Fail(st, ovals.value);

          var (st1, values) := Pes_Step(st, ovals.value);
          var st2 := StateSaveToRollback(st1, vars);

          // Slightly convoluted case: we need to provide `st3 == VS_UpdateStatePre(st2, vars, values)`
          // to `InductVarDecl_Some_Succ`, but `UpdateState` has a precondition which is given by the
          // postcondition of `InductUpdate_Succ`.
          if !VS_UpdateStatePre(st2, vars, values) {
            var st3 := st2; // Dummy
            InductVarDecl_Some_Succ(st, e, vdecls, vars, ovals.value, st1, values, st2, st3); // This leads to a contradiction
            assert false;
          }
          else {
            var st3 := UpdateState(st2, vars, values);
            InductVarDecl_Some_Succ(st, e, vdecls, vars, ovals.value, st1, values, st2, st3);
          }
        }
        else {
          var st1 := StateSaveToRollback(st, vars);
          InductVarDecl_None_Succ(st, e, vdecls, vars, st1);
        }

      case Update(vars, vals) =>
        // Recursion
        Pes_Satisfied(st, vals);

        InductUpdate_Fail(st, e, vars, vals);
        assert !Pes_Fail(st, vals);
        var (st1, values) := Pes_Step(st, vals);

        // Slightly convoluted case: we need to provide `st2 == UpdateState(st1, vars, values)`
        // to `InductUpdate_Succ`, but `UpdateState` has a precondition which is given by the
        // postcondition of `InductUpdate_Succ`.
        if !VS_UpdateStatePre(st1, vars, values) {
          var st2 := st1; // Dummy
          InductUpdate_Succ(st, e, vars, vals, st1, values, st2); // This leads to a contradiction
          assert false;
        }
        else {
          var st2 := UpdateState(st1, vars, values);
          InductUpdate_Succ(st, e, vars, vals, st1, values, st2);
        }

      case Bind(bvars, bvals, bbody) =>
        var vars := VarsToNames(bvars);

        assert Exprs.Exprs_Size(bvals) < e.Size();

        Pes_Satisfied(st, bvals); // Recursion
        assert !Pes_Fail(st, bvals) by { InductBind_Fail(st, e, bvars, bvals, bbody, vars); }

        var (st1, vals) := Pes_Step(st, bvals);
        assert VS_UpdateStatePre(st1, vars, vals) by { InductBind_Fail(st, e, bvars, bvals, bbody, vars); }

        var st2 := UpdateState(st1, vars, vals);
        P_Satisfied(st2, bbody); // Recursion
        assert !P_Fail(st2, bbody) by { InductBind_Fail(st, e, bvars, bvals, bbody, vars); }

        var (st3, v) := P_Step(st2, bbody);
        var st4 := StateBindEndScope(st1, st3, vars);

        InductBind_Succ(st, e, bvars, bvals, bbody, vars, st1, vals, st2, st3, v, st4);
  
      case Block(stmts) =>
        var st_start := StateStartScope(st);

        // Recursion
        Pes_Satisfied(st_start, stmts);
        
        InductBlock_Fail(st, e, stmts, st_start);
        assert !Pes_Fail(st_start, stmts);

        var (st_stmts, vs) := Pes_Step(st_start, stmts);
        var vf := if vs == NilVS then UnitV else VS_Last(vs);

        var st_end := StateEndScope(st, st_stmts);
        InductBlock_Succ(st, e, stmts, st_start, st_stmts, vs, st_end, vf);
        assert P_Succ(st, e, st_end, vf);
        P_Succ_Sound(st, e, st_end, vf);
    }
  }

  lemma Pes_Satisfied(st: S, es: seq<Expr>)
    ensures Pes(st, es)
    decreases Exprs.Exprs_Size(es), 3
  {
    if Pes_Fail(st, es) {
      Pes_Fail_Sound(st, es);
    }
    else {
      Pes_Satisfied_Succ(st, es);
    }
  }

  lemma Pes_Satisfied_Succ(st: S, es: seq<Expr>)
    requires !Pes_Fail(st, es)
    ensures Pes(st, es)
    decreases Exprs.Exprs_Size(es), 2
  {
    if es == [] {
      InductExprs_Nil(st);
      assert Pes_Succ(st, [], st, NilVS);
      Pes_Succ_Sound(st, [], st, NilVS);
    }
    else {
      var e := es[0];
      var es' := es[1..];
      assert [e] + es' == es;

      P_Satisfied(st, e); // Recursion

      if P_Fail(st, e) {
        InductExprs_Cons(st, e, es');
        assert Pes_Fail(st, [e] + es');
        Pes_Fail_Sound(st, [e] + es');
      }
      else {
        var (st1, v) := P_Step(st, e);
        Pes_Satisfied(st1, es'); // Recursion

        if Pes_Fail(st1, es') {
          InductExprs_Cons(st, e, es');
          assert Pes_Fail(st, [e] + es');
          Pes_Fail_Sound(st, [e] + es');
        }
        else {
          var (st2, vs) := Pes_Step(st1, es');
          InductExprs_Cons(st, e, es');
          assert Pes_Succ(st, [e] + es', st2, AppendValue(v, vs));
          Pes_Succ_Sound(st, [e] + es', st2, AppendValue(v, vs));
        }
      }
    }
  }
} // end of module Bootstrap.Semantics.ExprInduction.Ind


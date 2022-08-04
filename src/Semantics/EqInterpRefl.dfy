include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "Interp.dfy"
include "Equiv.dfy"
include "ExprInduction.dfy"
include "EqInterpScopes.dfy"

module Bootstrap.Semantics.EqInterpRefl {
  // This module provides lemmas which state that evaluating an expression with equivalent contexts
  // (in the sense of ``EqState``) leads to equivalent results.
  //
  // We simply reuse the results from `EqInterpScopes`, which are stricly more general.

  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import opened Interp
  import opened Values
  import opened Equiv
  import opened Utils.Lib.Datatypes
  import opened EqInterpScopes

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

    reveal GEqCtx();
    Base.Pes_Satisfied(Base.MState(env, map [], ctx, map [], ctx'), es);

    reveal InterpExprs_Block();
  }

  lemma InterpExprs_EqRefl(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
    requires EqState(ctx, ctx')
    ensures EqInterpResultSeqValue(InterpExprs(es, env, ctx), InterpExprs(es, env, ctx'))
  {
    reveal GEqCtx();
    Base.Pes_Satisfied(Base.MState(env, map [], ctx, map [], ctx'), es);
  }

  // DISCUSS: the proof actually indirectly relies on the fact that ``EqValue`` is reflexive.
  // But the proof that ``EqValue`` is reflexive (not done) relies, for the closure case, on the fact
  // that ``EqInterp`` is reflexive. The termination argument is not trivial, and we may have to
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
    reveal GEqCtx();
    Base.P_Satisfied(Base.MState(env, map [], ctx, map [], ctx'), e);
  }

} // end of module Bootstrap.Semantics.EqInterpRefl

include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "Interp.dfy"
include "Equiv.dfy"
include "ExprInduction.dfy"

// This file provides lemmas which prove that the environment is monotonous (the set of
// variables grows).

module Bootstrap.Semantics.InterpStateIneq.Base refines ExprInduction {
  //
  // Declarations
  //
  type Value = Interp.Value

  datatype MState = MState(env: Environment, ctx: State)

  type S(!new) = MState
  type V(!new) = Value
  type VS(!new) = seq<Value>

  predicate StateSmaller(ctx: State, ctx': State)
  {
    // We have to pay attention to one thing, which is that when we evaluate a variable declaration,
    // we *remove* the binding from the local variables, but if this binding is already present,
    // we save it in the rollback.
    && ctx.locals.Keys + ctx.rollback.Keys <= ctx'.locals.Keys + ctx'.rollback.Keys
    && ctx.rollback.Keys <= ctx'.rollback.Keys
  }

  predicate InterpResultStateSmaller<V>(ctx: State, res: InterpResult<V>)
  {
    match res
      case Success(Return(_, ctx')) => StateSmaller(ctx, ctx')
      case Failure(_) => true
  }

  predicate P(st: S, e: Expr)
  {
    InterpResultStateSmaller(st.ctx, InterpExpr(e, st.env, st.ctx))
  }
  
  predicate P_Succ(st: S, e: Expr, st': S, v: V)
  {
    && InterpResultStateSmaller(st.ctx, InterpExpr(e, st.env, st.ctx))
    && InterpExpr(e, st.env, st.ctx) == Success(Return(v, st'.ctx))
    && st.env == st'.env
  }

  predicate P_Fail(st: S, e: Expr)
  {
    InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate Pes(st: S, es: seq<Expr>)
  {
    InterpResultStateSmaller(st.ctx, InterpExprs(es, st.env, st.ctx))
  }

  predicate Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
  {
    && InterpResultStateSmaller(st.ctx, InterpExprs(es, st.env, st.ctx))
    && InterpExprs(es, st.env, st.ctx) == Success(Return(vs, st'.ctx))
    && st.env == st'.env
  }

  predicate Pes_Fail(st: S, es: seq<Expr>)
  {
    InterpExprs(es, st.env, st.ctx).Failure?
  }

  function AppendValue ...
  {
    [v] + vs
  }

  function SeqVToVS ...
  {
    vs
  }
  
  function GetNilVS ...
  {
    []
  }

  ghost const UnitV := Values.Unit

  function VS_Last ...
  {
    vs[|vs| - 1]
  }

  predicate VS_UpdateStatePre ...
  {
    && |argvs| == |vars|
  }

  function BuildClosureCallState ...
  {
    var ctx1 := BuildCallState(st.ctx.locals, vars, argvs);
    MState(st.env, ctx1)
  }

  function UpdateState ...
  {
    var ctx1 := st.ctx.(locals := AugmentContext(st.ctx.locals, vars, vals));
    MState(st.env, ctx1)
  }

  function StateSaveToRollback ...
  {
    var ctx := SaveToRollback(st.ctx, vars);
    var st' := MState(st.env, ctx);
    st'
  }

  function StateBindEndScope ...
  {
    var ctx' := st.ctx.(locals := CtxBindEndScope(st0.ctx.locals, st.ctx.locals, vars));
    var st' := MState(st.env, ctx');
    st'
  }

  function StateStartScope ...
  {
    var ctx := StartScope(st.ctx);
    MState(st.env, ctx)
  }

  function StateEndScope ...
  {
    var ctx := EndScope(st0.ctx, st.ctx);
    MState(st.env, ctx)
  }

  function P_Step ... {
    var Return(v, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    (MState(st.env, ctx1), v)
  }

  function Pes_Step ... {
    var Return(vs, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    (MState(st.env, ctx1), vs)
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

  lemma InductVar ... { reveal InterpExpr(); }

  lemma InductLiteral ... { reveal InterpExpr(); }

  lemma InductAbs ... { reveal InterpExpr(); }

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

  lemma InductApplyEagerUnaryOp_Succ ... { reveal InterpExpr(); }
  lemma InductApplyEagerBinaryOp_Succ ... { reveal InterpExpr(); }
  lemma InductApplyEagerTernaryOp_Succ ... { reveal InterpExpr(); }
  lemma InductApplyEagerBuiltinDisplay ... { reveal InterpExpr(); }
  lemma InductApplyEagerFunctionCall ... { reveal InterpExpr(); }

  lemma InductIf_Fail ... { reveal InterpExpr(); }
  lemma InductIf_Succ ... { reveal InterpExpr(); }

  lemma InductUpdate_Fail ... { reveal InterpExpr(); }
  lemma InductUpdate_Succ ... { reveal InterpExpr(); }

  lemma InductVarDecl_None_Succ ... { reveal InterpExpr(); reveal SaveToRollback(); }
  lemma InductVarDecl_Some_Fail ... { reveal InterpExpr(); }
  lemma InductVarDecl_Some_Succ  ... { reveal InterpExpr(); reveal SaveToRollback(); }

  lemma InductBind_Fail ... { reveal InterpExpr(); }
  lemma InductBind_Succ ... {
    reveal InterpExpr();
    // In practice we could ignore this case: we need to prove this monotonicity property in the case
    // where we have variable declarations, not variable bindings. But it is quite convenient that
    // the property is true when also having variable bindings: it makes the work simpler.
    assert st4.ctx.locals == st1.ctx.locals + (st3.ctx.locals - set v | v in vars);
    assert st1.ctx.locals.Keys <= st4.ctx.locals.Keys;
    assert st1.ctx.rollback.Keys <= st4.ctx.rollback.Keys;

    assert e == Expr.Bind(bvars, bvals, bbody);
    var MState(env, ctx) := st;
    // TODO(SMH): something very strange is happening here: we need to call ``InterpBind_Correct``
    // and reveal ``InterpBind``: it is as if revealing ``InterpExpr`` does nothing!?
    assert InterpExpr(e, env, ctx) == InterpBind(e, env, ctx) by { InterpBind_Correct(e, env, ctx); }
    reveal InterpBind();
    assert InterpExpr(e, env, ctx) == Success(Return(v, st4.ctx));
  }

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
  }

  lemma InductBlock_Succ ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
  }

} // end of module Bootstrap.Semantics.EqInterpRefl.Base

module Bootstrap.Semantics.InterpStateIneq {
  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import opened Interp
  import opened Values
  import opened Equiv
  import opened Utils.Lib.Datatypes
  import opened Base

  type Expr = Interp.Expr
  ghost const StateSmaller := Base.StateSmaller
  predicate InterpResultStateSmaller<V>(ctx: State, res: InterpResult<V>)
  {
    Base.InterpResultStateSmaller(ctx, res)
  }

  lemma InterpBlock_Exprs_StateSmaller(es: seq<Expr>, env: Environment, ctx: State)
    // TODO(SMH): for some reason, using ``Seq_All`` makes some proofs fail. The weird thing is
    // that I can then prove `Seq_All(SupportsInterp, es)` in an assertion just before the call
    // to the lemma, but the lemma precondition keeps failing.
    requires forall e | e in es :: SupportsInterp(e)
    ensures InterpResultStateSmaller(ctx, InterpBlock_Exprs(es, env, ctx))
  {
    InterpExprs_Block_Equiv_Strong(es, env, ctx);
    Base.Pes_Satisfied(MState(env, ctx), es);

    reveal InterpExprs_Block();
  }

  lemma InterpExprs_StateSmaller(es: seq<Expr>, env: Environment, ctx: State)
    ensures InterpResultStateSmaller(ctx, InterpExprs(es, env, ctx))
  {
    Base.Pes_Satisfied(MState(env, ctx), es);
  }

  lemma InterpExpr_StateSmaller(e: Expr, env: Environment, ctx: State)
    ensures InterpResultStateSmaller(ctx, InterpExpr(e, env, ctx))
  {
    Base.P_Satisfied(MState(env, ctx), e);
  }

} // end of module Bootstrap.Semantics.EqInterpRefl

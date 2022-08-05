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
  type {:verify false} Value = Interp.Value

  datatype {:verify false} MState = MState(env: Environment, ctx: State)

  type {:verify false} S(!new) = MState
  type {:verify false} V(!new) = Value
  type {:verify false} VS(!new) = seq<Value>

  predicate {:verify false} StateSmaller(ctx: State, ctx': State)
  {
    // We have to pay attention to one thing, which is that when we evaluate a variable declaration,
    // we *remove* the binding from the local variables, but if this binding is already present,
    // we save it in the rollback.
    && ctx.locals.Keys + ctx.rollback.Keys <= ctx'.locals.Keys + ctx'.rollback.Keys
    && ctx.rollback.Keys <= ctx'.rollback.Keys
  }

  predicate {:verify false} InterpResultStateSmaller<V>(ctx: State, res: InterpResult<V>)
  {
    match res
      case Success(Return(_, ctx')) => StateSmaller(ctx, ctx')
      case Failure(_) => true
  }

  predicate {:verify false} P(st: S, e: Expr)
  {
    InterpResultStateSmaller(st.ctx, InterpExpr(e, st.env, st.ctx))
  }
  
  predicate {:verify false} P_Succ(st: S, e: Expr, st': S, v: V)
  {
    && InterpResultStateSmaller(st.ctx, InterpExpr(e, st.env, st.ctx))
    && InterpExpr(e, st.env, st.ctx) == Success(Return(v, st'.ctx))
    && st.env == st'.env
  }

  predicate {:verify false} P_Fail(st: S, e: Expr)
  {
    InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate {:verify false} Pes(st: S, es: seq<Expr>)
  {
    InterpResultStateSmaller(st.ctx, InterpExprs(es, st.env, st.ctx))
  }

  predicate {:verify false} Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
  {
    && InterpResultStateSmaller(st.ctx, InterpExprs(es, st.env, st.ctx))
    && InterpExprs(es, st.env, st.ctx) == Success(Return(vs, st'.ctx))
    && st.env == st'.env
  }

  predicate {:verify false} Pes_Fail(st: S, es: seq<Expr>)
  {
    InterpExprs(es, st.env, st.ctx).Failure?
  }

  function {:verify false} AppendValue ...
  {
    [v] + vs
  }

  function {:verify false} SeqVToVS ...
  {
    vs
  }
  
  function {:verify false} GetNilVS ...
  {
    []
  }

  ghost const {:verify false} UnitV := Values.Unit

  function {:verify false} VS_Last ...
  {
    vs[|vs| - 1]
  }

  predicate {:verify false} VS_UpdateStatePre ...
  {
    && |argvs| == |vars|
  }

  function {:verify false} BuildClosureCallState ...
  {
    var ctx1 := BuildCallState(st.ctx.locals, vars, argvs);
    MState(st.env, ctx1)
  }

  function {:verify false} UpdateState ...
  {
    var ctx1 := st.ctx.(locals := AugmentContext(st.ctx.locals, vars, vals));
    MState(st.env, ctx1)
  }

  function {:verify false} StateSaveToRollback ...
  {
    var ctx := SaveToRollback(st.ctx, vars);
    var st' := MState(st.env, ctx);
    st'
  }

  function {:verify false} StateBindEndScope ...
  {
//    var ctx' := st.ctx.(locals := CtxBindEndScope(st0.ctx.locals, st.ctx.locals, vars));
//    assert ctx' == st.ctx.(locals := st0.ctx.locals + (st.ctx.locals - set v | v in vars));
    var ctx' := st.ctx.(locals := st0.ctx.locals + (st.ctx.locals - set v | v in vars));
    var st' := MState(st.env, ctx');
    st'
  }

  function {:verify false} StateStartScope ...
  {
    var ctx := StartScope(st.ctx);
    MState(st.env, ctx)
  }

  function {:verify false} StateEndScope ...
  {
    var ctx := EndScope(st0.ctx, st.ctx);
    MState(st.env, ctx)
  }

  function {:verify false} P_Step ... {
    var Return(v, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    (MState(st.env, ctx1), v)
  }

  function {:verify false} Pes_Step ... {
    var Return(vs, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    (MState(st.env, ctx1), vs)
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

  lemma {:verify false} InductVar ... { reveal InterpExpr(); }

  lemma {:verify false} InductLiteral ... { reveal InterpExpr(); }

  lemma {:verify false} InductAbs ... { reveal InterpExpr(); }

  lemma {:verify false} InductAbs_CallState ... {
    reveal InterpExpr();
    reveal InterpCallFunctionBody();
    reveal BuildCallState();
  }

  lemma {:verify false} InductExprs_Nil ... { reveal InterpExprs(); }
  lemma {:verify false} InductExprs_Cons ... { reveal InterpExprs(); }

  lemma {:verify false} InductApplyLazy_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductApplyLazy_Succ ... { reveal InterpExpr(); }

  lemma {:verify false} InductApplyEager_Fail ... { reveal InterpExpr(); }

  lemma {:verify false} InductApplyEagerUnaryOp_Succ ... { reveal InterpExpr(); }
  lemma {:verify false} InductApplyEagerBinaryOp_Succ ... { reveal InterpExpr(); }
  lemma {:verify false} InductApplyEagerTernaryOp_Succ ... { reveal InterpExpr(); }
  lemma {:verify false} InductApplyEagerBuiltinDisplay ... { reveal InterpExpr(); }
  lemma {:verify false} InductApplyEagerFunctionCall ... { reveal InterpExpr(); }

  lemma {:verify false} InductIf_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductIf_Succ ... { reveal InterpExpr(); }

  lemma {:verify false} InductUpdate_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductUpdate_Succ ... { reveal InterpExpr(); }

  lemma {:verify false} InductVarDecl_None_Succ ... { reveal InterpExpr(); reveal SaveToRollback(); }
  lemma {:verify false} InductVarDecl_Some_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductVarDecl_Some_Succ  ... { reveal InterpExpr(); reveal SaveToRollback(); }

  lemma {:verify false} InductBind_Fail ... { reveal InterpExpr(); }
  lemma {:verify true} InductBind_Succ ... {
    reveal InterpExpr();
    // In practice we could ignore this case: we need to prove this monotonicity property in the case
    // where we have variable declarations, not variable bindings. But it is quite convenient that
    // the property is true when also having variable bindings: it makes the work simpler.
    assert st4.ctx.locals == st1.ctx.locals + (st3.ctx.locals - set v | v in vars);
//    assert st4.ctx == st4.ctx.(locals := CtxBindEndScope(st1.ctx.locals, st3.ctx.locals, vars));
    assert st1.ctx.locals.Keys <= st4.ctx.locals.Keys;
    assert st1.ctx.rollback.Keys <= st4.ctx.rollback.Keys;
/*    assert StateSmaller(st.ctx, st1.ctx);
    assert StateSmaller(st1.ctx, st4.ctx);
    assert StateSmaller(st.ctx, st4.ctx);
//    assert InterpExpr(e, st.env, st.ctx) == Success(Return(v, st4.ctx));

    var MState(env, ctx) := st;
    var Return(vals, ctx1) := InterpExprs(bvals, env, ctx).value;
    var ctx2 := ctx1.(locals := AugmentContext(ctx1.locals, vars, vals));
    var Return(val, ctx3) := InterpExpr(bbody, env, ctx2).value;
    var ctx4 := ctx3.(locals := CtxBindEndScope(ctx1.locals, ctx3.locals, vars));
    assert InterpExpr(e, st.env, st.ctx) == Success(Return(val, ctx4));

    assume false;*/
    //assert P_Succ(st, e, st4, v);
//    assume false;
//    assume false;
//    assert st.ctx.locals.Keys + st.ctx.rollback.Keys <= st1.ctx.
//    assume false;
  }

  // TODO(SMH): I tried simplifying the proofs below by adding a `requires` in ``InductBlock_Fail``
  // and ``InductBlock_Succ`` to provide the result of calling ``InterpExprs_Block_Equiv_Strong``,
  // but it didn't work due to SMT solvers' misteries.
  lemma {:verify false} InductBlock_Fail ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();

    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
  }

  lemma {:verify false} InductBlock_Succ ...
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

  type {:verify false} Expr = Interp.Expr
  ghost const {:verify false} StateSmaller := Base.StateSmaller
  predicate {:verify false} InterpResultStateSmaller<V>(ctx: State, res: InterpResult<V>)
  {
    Base.InterpResultStateSmaller(ctx, res)
  }

  lemma {:verify false} InterpBlock_Exprs_StateSmaller(es: seq<Expr>, env: Environment, ctx: State)
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

  lemma {:verify false} InterpExprs_StateSmaller(es: seq<Expr>, env: Environment, ctx: State)
    ensures InterpResultStateSmaller(ctx, InterpExprs(es, env, ctx))
  {
    Base.Pes_Satisfied(MState(env, ctx), es);
  }

  lemma {:verify false} InterpExpr_StateSmaller(e: Expr, env: Environment, ctx: State)
    ensures InterpResultStateSmaller(ctx, InterpExpr(e, env, ctx))
  {
    Base.P_Satisfied(MState(env, ctx), e);
  }

} // end of module Bootstrap.Semantics.EqInterpRefl

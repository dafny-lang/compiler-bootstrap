//include "../Interop/CSharpDafnyASTModel.dfy"
//include "../Interop/CSharpInterop.dfy"
//include "../Interop/CSharpDafnyInterop.dfy"
//include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Semantics/ExprInduction.dfy"
//include "InterpStateIneq.dfy"

module Bootstrap.Transforms.InlineVar.Base {
  import opened AST.Syntax
  import opened Utils.Lib
  import opened Utils.Lib.Datatypes
  import opened AST.Predicates
  import Semantics.Interp
  import opened Semantics.Equiv
  import opened Generic
  import Shallow

  type Environment = Interp.Environment
  type State = Interp.State
  type Expr = Interp.Expr
  const VarsToNames := Interp.VarsToNames

  // TODO(SMH): move?
  function method VarsOfExpr(e: Expr): set<string>
    decreases e.Size(), 0
    // Return the set of all variables used in an expression (accessed, updated or even declared)
  {
    reveal Interp.SupportsInterp();
    Expr.Size_Decreases(e); // For termination
    match e {
      case Var(v) => {v}
      case Literal(_) => {}
      case Abs(vars, body) => (set x | x in vars) + VarsOfExpr(body)
      case Apply(aop, exprs) =>
        VarsOfExprs(exprs)
      case Block(exprs) =>
        VarsOfExprs(exprs)
      case VarDecl(vdecls, ovals) =>
        var s := if ovals.Some? then VarsOfExprs(ovals.value) else {};
        s + set x | x in VarsToNames(vdecls)
      case Update(vars, vals) =>
        (set x | x in vars) + VarsOfExprs(vals)
      case Bind(vars, vals, body) =>
        (set x | x in VarsToNames(vars)) + VarsOfExprs(vals) + VarsOfExpr(body)
      case If(cond, thn, els) =>
        VarsOfExpr(cond) + VarsOfExpr(thn) + VarsOfExpr(els)
    }
  }

  function method VarsOfExprs(es: seq<Expr>): set<string>
    decreases Expr.Exprs_Size(es), 1
  {
    if es == [] then {}
    else VarsOfExpr(es[0]) + VarsOfExprs(es[1..])
  }

  type Subst = map<string, Expr>
  const EmptyBlock: Interp.Expr := reveal Interp.SupportsInterp(); Expr.Block([])

  predicate method CanInlineVar(p: (Exprs.Var, Expr) -> bool, after: set<string>, v: Exprs.Var, rhs: Expr)
  {
    && p(v, rhs) // The filtering predicate allows to inline this variable
    && v.name !in after // The variable is not shadowed later
    && (VarsOfExpr(rhs) * after) == {} // The variables used in the rhs are not shadowed later
  }

  function method AddToSubst(subst: Subst, v: Exprs.Var, rhs: Expr): Subst
  {
    subst[v.name := rhs]
  }
  
  function method InlineInExpr(p: (Exprs.Var, Expr) -> bool, subst: Subst, after: set<string>, e: Expr):
    Result<(Subst, Expr), ()>
    decreases e.Size(), 0
    // Inline the variables on which `p` evaluates to `true`, if possible.
    //
    // For now we do something quite simple.
    //
    // - `subst`: the accumulated substitutions
    // - `after`: the set of variables present in the expressions that will get evaluated *after* `e`
  {
    reveal Interp.SupportsInterp();
    Expr.Size_Decreases(e); // For termination
    match e {
      case Var(v) =>
        if v in subst.Keys then Success((subst, subst[v])) else Success((subst, e))

      case Literal(_) => Success((subst, e))

      case Abs(vars, body) =>
        var (_, body') :- InlineInExpr(p, subst, {}, body);
        Success((subst, e.(body := body')))

      case Apply(aop, args) =>
        var (subst', args') :- InlineInExprs(p, subst, after, args);
        Success((subst', e.(args := args')))

      case Block(stmts) =>
        var (_, stmts') :- InlineInExprs(p, subst, {}, stmts);
        Success((subst, e.(stmts := stmts')))

      case VarDecl(vdecls, ovals) =>
        if ovals.Some? then
          var (subst1, vals') :- InlineInExprs(p, subst, after, ovals.value);
          // For now, we inline only if there is exactly one variable
          if |vdecls| == 1 && CanInlineVar(p, after, vdecls[0], vals'[0]) then
            var subst2 := AddToSubst(subst, vdecls[0], vals'[0]);
            Success((subst2, EmptyBlock))
          else Success((subst1, Expr.VarDecl(vdecls, Exprs.Some(vals'))))
        else Success((subst, e))

      case Update(vars, vals) =>
        var (subst', vals') :- InlineInExprs(p, subst, after, vals);
        Success((subst', e.(vals := vals')))

      case Bind(bvars, bvals, bbody) =>
        var body_vars := VarsOfExpr(bbody);
        var after1 := after + body_vars;
        var (subst1, bvals') :- InlineInExprs(p, subst, after1, bvals);
        // For now, we inline only if there is exactly one variable
        // Rk.: we return the original subst because there is a scope
        if |bvars| == 1 && CanInlineVar(p, after1, bvars[0], bvals'[0]) then
            var subst2 := AddToSubst(subst, bvars[0], bvals'[0]);
            var (subst3, bbody') :- InlineInExpr(p, subst2, after, bbody);
            Success((subst, Expr.Block([bbody'])))
        else
          var (subst2, bbody') :- InlineInExpr(p, subst1, after, bbody);
          Success((subst, Expr.Bind(bvars, bvals', bbody')))

      case If(cond, thn, els) =>
        var thn_vars := VarsOfExpr(thn);
        var els_vars := VarsOfExpr(els);
        var (subst1, cond') :- InlineInExpr(p, subst, after + thn_vars + els_vars, cond);
        var (_, thn') :- InlineInExpr(p, subst1, after, thn);
        var (_, els') :- InlineInExpr(p, subst1, after, els);
        // TODO: we must check that no variables leak from the branches
        Success((subst1, Expr.If(cond', thn', els')))
    }
  }

  function method InlineInExprs(p: (Exprs.Var, Expr) -> bool, subst: Subst, after: set<string>, es: seq<Expr>) :
    (out: Result<(Subst, seq<Expr>), ()>)
    decreases Expr.Exprs_Size(es), 1
    ensures
      match out {
        case Success((_, es')) => |es'| == |es|
        case Failure(_) => true
      }
  {
    if es == [] then Success((subst, []))
    else
      var after' := after + VarsOfExprs(es[1..]); // This is terribly inefficient...
      var (subst1, e') :- InlineInExpr(p, subst, after', es[0]);
      var (subst2, es') :- InlineInExprs(p, subst1, after, es[1..]);
      Success((subst2, [e'] + es'))
  }
}

module Bootstrap.Transforms.InlineVar.BaseProofs { // refines Semantics.ExprInduction {
  // TODO: remove //
  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import opened Semantics.Interp
  import opened Semantics.Values
  import opened Semantics.Equiv
  import opened Utils.Lib.Datatypes
  type Expr = Interp.Expr
  // END of TODO: remove //

/*  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import Semantics.Interp
  import opened Semantics.Equiv
  import opened Generic
  import Shallow*/
  import opened Base

  type Value = Interp.Value
  type Context = Interp.Context
  const VarsToNames := Interp.VarsToNames

//  const EmptyCtx: Context := map[]

  // - `ctx`: the environment to execute the original expression
  // - `ctx'`: the environment to execute the expression on which we performed inlinings
  // - `after`: the set of variables in the expressions to evaluate after the current one
  datatype MState = MState(env: Environment, subst: Subst, after: set<string>, ctx: State, ctx': State)
  datatype MValue = MValue(v: Value, v': Value)
  datatype MSeqValue = MSeqValue(vs: seq<Value>, vs': seq<Value>)

/*  predicate EqOuterRollback(outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
  {
    EqCtx(ctx.rollback + outer_rollback, ctx'.rollback + outer_rollback')
  }*/

/*
  // TODO(SMH): move?
  predicate {:opaque} EqSubCtx(keys: set<string>, ctx: Context, ctx': Context)
  {
    && keys <= ctx.Keys
    && keys <= ctx'.Keys
    && forall x | x in keys :: EqValue(ctx[x], ctx'[x])
  }

  // TODO(SMH): move? This is not used in this module. But this should be kept with ``EqOuterRollback``
  predicate EqRolled(keys: set<string>, ctx: State, ctx': State)
  {
    EqSubCtx(keys, ctx.locals + ctx.rollback, ctx'.locals + ctx'.rollback)
  }*/

  predicate {:opaque} EqStateOnSubst(env: Environment, subst: Subst, ctx: State, ctx': State)
    requires subst.Keys <= ctx.locals.Keys
  {
    forall x | x in subst.Keys ::
      var res := InterpExpr(subst[x], env, ctx');
      match res {
        case Success(Return(v, ctx'')) =>
          && ctx'' == ctx'
          && v == ctx.locals[x]
        case Failure(_) => false
      }
  }

  predicate EqStateWithSubst(env: Environment, subst: Subst, ctx: State, ctx': State)
  {
    && EqCtx(ctx.rollback, ctx'.rollback)
    && ctx'.locals.Keys !! subst.Keys
    && ctx'.locals.Keys + subst.Keys == ctx.locals.Keys
    && EqCtx(map x | x in ctx'.locals.Keys :: ctx.locals[x], ctx'.locals)
    && EqStateOnSubst(env, subst, ctx, ctx')
  }

  predicate Inv(st: MState)
  {
    EqStateWithSubst(st.env, st.subst, st.ctx, st.ctx')
  }

  predicate {:opaque} StateRel(st: MState, st': MState)
  {
    && st.subst.Keys <= st'.subst.Keys
    && forall x | x in st.subst.Keys :: st'.subst[x] == st.subst[x]
  }

/*
  predicate EqResult<V>(eq_value: (V,V) -> bool, subst: Subst, res: InterpResult<V>, res': InterpResult<V>)
  {
    match (res, res')
      case (Success(Return(v, ctx)), Success(Return(v', ctx'))) =>
        && eq_value(v, v')
        && EqCtx(ctx.locals, ctx'.locals)
        && EqOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
      case (Failure(_), _) => true
      case _ => false
  }

  predicate EqResultValue(outer_rollback: Context, res: InterpResult<Value>, outer_rollback': Context, res': InterpResult<Value>)
  {
    EqResult(EqValue, outer_rollback, res, outer_rollback', res')
  }

  predicate EqResultSeqValue(outer_rollback: Context, res: InterpResult<seq<Value>>, outer_rollback': Context, res': InterpResult<seq<Value>>)
  {
    EqResult(EqSeqValue, outer_rollback, res, outer_rollback', res')
  }

  // TODO(SMH): factorize with EqResult and move. The annoying thing is that functions are not curried, so it makes
  // facorization a bit hard...
  predicate EqResultRolled<V>(eq_value: (V,V) -> bool, keys: set<string>, res: InterpResult<V>, res': InterpResult<V>)
  {
    match (res, res')
      case (Success(Return(v, ctx)), Success(Return(v', ctx'))) =>
        && eq_value(v, v')
        && EqRolled(keys, ctx, ctx')
      case (Failure(_), _) => true
      case _ => false
  }

  predicate EqResultRolledValue(keys: set<string>, res: InterpResult<Value>, res': InterpResult<Value>)
  {
    EqResultRolled(EqValue, keys, res, res')
  }

  predicate EqResultRolledSeqValue(keys: set<string>, res: InterpResult<seq<Value>>, res': InterpResult<seq<Value>>)
  {
    EqResultRolled(EqSeqValue, keys, res, res')
  }


  predicate Inv(st: MState)
  {
    && EqCtx(st.ctx.locals, st.ctx'.locals)
    && EqOuterRollback(st.outer_rollback, st.ctx, st.outer_rollback', st.ctx')
  }*/

  type S(!new) = MState
  type V(!new) = MValue
  type VS(!new) = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

/*  predicate P(st: S, e: Expr)
  {
    var res := InterpExpr(e, st.env, st.ctx);
    var res' := InterpExpr(e, st.env, st.ctx');
    && Inv(st) ==>
//    match (res, res') {
//      Success(Return(v, ctx1), ctx1'
//    }
//    EqResultValue(st.outer_rollback, res, st.outer_rollback', res')
  }
  
  predicate P_Succ(st: S, e: Expr, st': S, v: V)
  {
    && Inv(st)
    && EqResultValue(st.outer_rollback, InterpExpr(e, st.env, st.ctx), st.outer_rollback', InterpExpr(e, st.env, st.ctx'))
    && InterpExpr(e, st.env, st.ctx) == Success(Return(v.v, st'.ctx))
    && InterpExpr(e, st.env, st.ctx') == Success(Return(v.v', st'.ctx'))
    && st.env == st'.env
    && st.outer_rollback == st'.outer_rollback
    && st.outer_rollback' == st'.outer_rollback'
  }

  predicate P_Fail(st: S, e: Expr)
  {
    Inv(st) ==> InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate Pes(st: S, es: seq<Expr>)
  {
    Inv(st) ==>
    EqResultSeqValue(st.outer_rollback, InterpExprs(es, st.env, st.ctx), st.outer_rollback', InterpExprs(es, st.env, st.ctx'))
  }

  predicate Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
  {
    && Inv(st)
    && EqResultSeqValue(st.outer_rollback, InterpExprs(es, st.env, st.ctx), st.outer_rollback', InterpExprs(es, st.env, st.ctx'))
    && InterpExprs(es, st.env, st.ctx) == Success(Return(vs.vs, st'.ctx))
    && InterpExprs(es, st.env, st.ctx') == Success(Return(vs.vs', st'.ctx'))
    && st.outer_rollback == st'.outer_rollback
    && st.outer_rollback' == st'.outer_rollback'
    && st.env == st'.env
  }

  predicate Pes_Fail(st: S, es: seq<Expr>)
  {
    Inv(st) ==> InterpExprs(es, st.env, st.ctx).Failure?
  }*/

  /*
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

  function UpdateState ...
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

  function StateSaveToRollback ...
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
        assert rolled.Keys == rolled'.Keys by { reveal GEqCtx(); } // Having this drastically reduces the proof time
        assert EqCtx(rolled, rolled') by { reveal GEqCtx(); } // Wow, this actually works
      }
    }

    st'
  }

  function StateStartScope ...
    ensures Inv(st) ==> Inv(st')
  {
    var ctx := StartScope(st.ctx);
    var ctx' := StartScope(st.ctx');
    reveal GEqCtx();
    MState(st.env, EmptyCtx, ctx, EmptyCtx, ctx')
  }

  function StateEndScope ...
    ensures Inv(st0) && Inv(st) && st.outer_rollback == st.outer_rollback' == EmptyCtx ==> Inv(st')
  {
    var ctx := EndScope(st0.ctx, st.ctx);
    var ctx' := EndScope(st0.ctx', st.ctx');
    reveal GEqCtx();
    MState(st.env, st0.outer_rollback, ctx, st0.outer_rollback', ctx')
  }

  function P_Step ... {
    var Return(v, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    var Return(v', ctx1') := InterpExpr(e, st.env, st.ctx').value;
    (MState(st.env, st.outer_rollback, ctx1, st.outer_rollback', ctx1'), MValue(v, v'))
  }

  function Pes_Step ... {
    var Return(vs, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    var Return(vs', ctx1') := InterpExprs(es, st.env, st.ctx').value;
    (MState(st.env, st.outer_rollback, ctx1, st.outer_rollback', ctx1'), MSeqValue(vs, vs'))
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

  lemma InductApplyEagerUnaryOp_Succ ... { reveal InterpExpr(); reveal InterpUnaryOp(); }

  lemma InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    InterpBinaryOp_Eq(e, e, op, v0.v, v1.v, v0.v', v1.v');
  }

  lemma {:fuel SeqVToVS, 2} InductApplyEagerTernaryOp_Succ ... {
    reveal InterpExpr();
    // TODO(SMH): ``SeqVToVS`` is called on literals: we shouldn't need fuel 2
    assert SeqVToVS([v0, v1, v2]) == MSeqValue([v0.v, v1.v, v2.v], [v0.v', v1.v', v2.v']);
    InterpTernaryOp_Eq(e, e, op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');
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

  lemma InductBind_Fail ... { reveal InterpExpr(); }
  lemma InductBind_Succ ... { reveal InterpExpr(); }

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
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx');
  }

  lemma InductBlock_Succ ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx');
  }*/
}

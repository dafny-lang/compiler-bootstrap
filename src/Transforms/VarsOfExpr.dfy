include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Semantics/ExprInduction.dfy"
include "../Semantics/InterpStateIneq.dfy"
include "../Semantics/EqInterpRefl.dfy"
include "../Semantics/Pure.dfy"

// TODO(SMH): I wanted to name this: `Bootstrap.Transforms.VarsOfExpr.Base`,
// and have a module `Bootstrap.Transforms.VarsOfExpr.Proofs`, but this causes
// trouble in `Bootstrap.Transforms.SubstVar.Subst.Proofs`, because I then want to
// to `import opened VarsOfExpr.Base`, but it conflicts with the
// `import opened Bootstrap.Transforms.SubstVar.Subst.Base`...
module Bootstrap.Transforms.VarsOfExpr {
  import opened AST.Syntax
  import opened Utils.Lib
  import opened Utils.Lib.Datatypes
  import opened AST.Predicates
  import Semantics.Interp
  import opened Semantics.Equiv
  import opened Semantics.Pure
  import opened Generic
  import Shallow

  type {:verify false} Environment = Interp.Environment
  type {:verify false} State = Interp.State
  type {:verify false} Expr = Interp.Expr

  function method {:verify false} {:opaque} SeqToSet<T>(s: seq<T>): set<T>
    // Unfortunately, we need this small opaque helper to prevent with proof explosions.
  {
    set x | x in s
  }

  function method {:verify false} {:opaque} VarsToNameSet(vars: seq<Exprs.TypedVar>): set<string>
    // Same as for ``SeqToSet``: making this definition opaque is annoying, but we need it to
    // prevent proof explosions.
  {
    set x | x in vars :: x.name
  }

  // TODO(SMH): move?
  function method {:verify false} VarsOfExpr(read: bool, e: Syntax.Expr): set<string>
    decreases e.Size(), 0
    // Return the set of all variables used in an expression (accessed, updated or even declared).
    //
    // `read`: if true, include in the set the variables which are read, otherwise ignore them.
  {
    reveal Interp.SupportsInterp();
    match e {
      case Var(v) => if read then {v} else {}
      case Literal(_) => {}
      case Abs(vars, body) =>
        (set x | x in vars) + VarsOfExpr(read, body)
      case Apply(aop, exprs) =>
        VarsOfExprs(read, exprs)
      case Block(exprs) =>
        VarsOfExprs(read, exprs)
      case VarDecl(vdecls, ovals) =>
        var s := if ovals.Some? then VarsOfExprs(read, ovals.value) else {};
        s + VarsToNameSet(vdecls)
      case Update(vars, vals) =>
        (set x | x in vars) + VarsOfExprs(read, vals)
      case Bind(vars, vals, body) =>
        VarsToNameSet(vars) + VarsOfExprs(read, vals) + VarsOfExpr(read, body)
      case If(cond, thn, els) =>
        VarsOfExpr(read, cond) + VarsOfExpr(read, thn) + VarsOfExpr(read, els)
    }
  }

  function method {:verify false} VarsOfExprs(read: bool, es: seq<Syntax.Expr>): set<string>
    decreases Expr.Exprs_Size(es), 1
  {
    if es == [] then {}
    else VarsOfExpr(read, es[0]) + VarsOfExprs(read, es[1..])
  }

  function method {:verify false} UpdtVarsOfExpr(e: Syntax.Expr): set<string>
  {
    VarsOfExpr(false, e)
  }

  function method {:verify false} UpdtVarsOfExprs(es: seq<Syntax.Expr>): set<string>
  {
    VarsOfExprs(false, es)
  }

  function method {:verify false} AllVarsOfExpr(e: Syntax.Expr): set<string>
  {
    VarsOfExpr(true, e)
  }

  function method {:verify false} AllVarsOfExprs(es: seq<Syntax.Expr>): set<string>
  {
    VarsOfExprs(true, es)
  }

  // Accumulator used for substitutions.
  // `subst`: the substitution
  // `frozen`: the variables which appear in the expressions with which we substitute
  datatype {:verify false} SubstAcc = SubstAcc(subst: map<string, Expr>)//, frozen: set<string>)

  predicate method {:verify false} NotVarDecl(e: Syntax.Expr)
  {
    !e.VarDecl?
  }
}

// Rem.(SMH): about the name, see the comment for `Bootstrap.Transforms.VarsOfExpr`
module Bootstrap.Transforms.VarsOfExprAddUselessBindings refines Semantics.ExprInduction {
  // TODO(SMH): update this comment
  // This module proves that:
  // If:
  // - we have an expression `e` and contexts `ctx` and `ctx'`
  // - `ctx'` is `ctx` augmented with bindings which don't appear in `e`
  // Then:
  // - evaluating `e` starting from `ctx` and `ctx'` leads to similar results

  import opened Semantics.Pure
//  import opened Base
  import opened VarsOfExpr
//  import Semantics.InterpStateIneq
//  import Semantics.EqInterpRefl

  type {:verify false} Value = Interp.Value

  type {:verify false} Context = Interp.Context

  const {:verify false} EmptyCtx: Context := map[]

  datatype {:verify false} MState = MState(env: Environment, add: map<string, Value>, ctx: State)
  datatype MValue = MValue(v: Value, v': Value)
  datatype MSeqValue = MSeqValue(vs: seq<Value>, vs': seq<Value>)

/*  predicate EqOuterRollback(outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
  {
    EqCtx(ctx.rollback + outer_rollback, ctx'.rollback + outer_rollback')
  }*/

/*  // TODO(SMH): move?
  predicate {:verify false} {:opaque} EqSubCtx(keys: set<string>, ctx: Context, ctx': Context)
  {
    && keys <= ctx.Keys
    && keys <= ctx'.Keys
    // Rem.(SMH): we use a strong equality
    && forall x | x in keys :: ctx[x] == ctx'[x] // EqValue(ctx[x], ctx'[x])
  }*/

/*  // TODO(SMH): move? This is not used in this module. But this should be kept with ``EqOuterRollback``
  predicate {:verify false} EqRolled(keys: set<string>, ctx: State, ctx': State)
  {
    EqSubCtx(keys, ctx.locals + ctx.rollback, ctx'.locals + ctx'.rollback)
  }*/

//  predicate EqOnAdd(add: map<string, Value>, ctx: State, ctx': State)

  predicate {:verify false} {:opaque} EqStateWithAdd(add: map<string, Value>, ctx: State, ctx': State)
  {
    //    && ctx.locals.Keys !! add.Keys
    && EqCtx(ctx.locals, ctx'.locals - add.Keys)
    && add.Keys <= ctx'.locals.Keys
    && forall x | x in add.Keys :: ctx'.locals[x] == add[x]
    && ctx.rollback == ctx'.rollback == map []
  }

/*  predicate EqResult<V>(eq_value: (V,V) -> bool, core: set<string>, res: InterpResult<V>, res': InterpResult<V>)
  {
    match (res, res')
      case (Success(Return(v, ctx)), Success(Return(v', ctx'))) =>
        && eq_value(v, v')
        && EqStateWithCore(core, ctx, ctx')
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

  // TODO(SMH): factorize with EqResult and move. The annoying thing is that functions are not curried, so it makes
  // facorization a bit hard...
  predicate {:verify false} EqResultRolled<V>(eq_value: (V,V) -> bool, keys: set<string>, res: InterpResult<V>, res': InterpResult<V>)
  {
    match (res, res')
      case (Success(Return(v, ctx)), Success(Return(v', ctx'))) =>
        && eq_value(v, v')
        && EqRolled(keys, ctx, ctx')
      case (Failure(_), _) => true
      case _ => false
  }

  predicate {:verify false} EqResultRolledValue(keys: set<string>, res: InterpResult<Value>, res': InterpResult<Value>)
  {
    EqResultRolled(EqValue, keys, res, res')
  }

  predicate {:verify false} EqResultRolledSeqValue(keys: set<string>, res: InterpResult<seq<Value>>, res': InterpResult<seq<Value>>)
  {
    EqResultRolled(EqSeqValue, keys, res, res')
  }*/

  predicate {:verify false} {:opaque} Inv(st: MState)
  {
    && st.ctx.locals.Keys !! st.add.Keys
    && st.ctx.rollback == map []
    //&& EqStateWithAdd(st.add, st.ctx)
  }

  predicate {:verify false} {:opaque} ExprValid(st: S, e: Expr)
  {
    && Deep.All_Expr(e, NotVarDecl)
    // We don't need to use the Deep predicate (it is actually equivalent to not using it) but
    // that makes the proofs easier.
    // TODO(SMH): prove the corresponding lemma
    && Deep.All_Expr(
      e, var f := (e: Syntax.Expr) => st.add.Keys !! AllVarsOfExpr(e); f)
  }

  predicate {:verify false} ExprsValid(st: S, es: seq<Expr>)
  {
    forall e | e in es :: ExprValid(st, e)
  }

  type {:verify false} S(!new) = MState
  type {:verify false} V(!new) = MValue
  type {:verify false} VS(!new) = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

  predicate {:verify false} P(st: S, e: Expr)
  {
    var ctx := st.ctx;
    var ctx' := ctx.(locals := ctx.locals + st.add);
    var res := InterpExpr(e, st.env, ctx);
    var res' := InterpExpr(e, st.env, ctx');
    Inv(st) ==>
    ExprValid(st, e) ==>
    && (match (res, res') {
        case (Success(Return(v1, ctx1)), Success(Return(v1', ctx1'))) =>
          var st1 := MState(st.env, st.add, ctx1);
          && EqValue(v1, v1')
          && Inv(st1)
          && EqStateWithAdd(st.add, ctx1, ctx1')
        case (Failure(_), _) => true
        case _ => false
      })
  }
  
  predicate {:verify false} P_Succ(st: S, e: Expr, st': S, v: V)
  {
    var ctx := st.ctx;
    var ctx' := ctx.(locals := ctx.locals + st.add);
    var res := InterpExpr(e, st.env, ctx);
    var res' := InterpExpr(e, st.env, ctx');
    && Inv(st)
    && ExprValid(st, e)
    && (match (res, res') {
        case (Success(Return(v1, ctx1)), Success(Return(v1', ctx1'))) =>
          var st1 := MState(st.env, st.add, ctx1);
          && EqValue(v1, v1')
          && Inv(st1)
          && EqStateWithAdd(st.add, ctx1, ctx1')
          // Additional
          && st1 == st'
          && v == MValue(v1, v1')
        case _ => false
      })
  }

  predicate {:verify false} P_Fail(st: S, e: Expr)
  {
    var ctx := st.ctx;
    var ctx' := ctx.(locals := ctx.locals + st.add);
    var res := InterpExpr(e, st.env, ctx);
    var res' := InterpExpr(e, st.env, ctx');
    Inv(st) ==>
    ExprValid(st, e) ==>
    res.Failure? && res'.Failure?
  }

  predicate {:verify false} Pes(st: S, es: seq<Expr>)
  {
    var ctx := st.ctx;
    var ctx' := ctx.(locals := ctx.locals + st.add);
    var res := InterpExprs(es, st.env, ctx);
    var res' := InterpExprs(es, st.env, ctx');
    Inv(st) ==>
    ExprsValid(st, es) ==>
    && (match (res, res') {
        case (Success(Return(vs1, ctx1)), Success(Return(vs1', ctx1'))) =>
          var st1 := MState(st.env, st.add, ctx1);
          && EqSeqValue(vs1, vs1')
          && Inv(st1)
          && EqStateWithAdd(st.add, ctx1, ctx1')
        case (Failure(_), _) => true
        case _ => false
      })
  }
  
  predicate {:verify false} Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
  {
    var ctx := st.ctx;
    var ctx' := ctx.(locals := ctx.locals + st.add);
    var res := InterpExprs(es, st.env, ctx);
    var res' := InterpExprs(es, st.env, ctx');
    && Inv(st)
    && ExprsValid(st, es)
    && (match (res, res') {
        case (Success(Return(vs1, ctx1)), Success(Return(vs1', ctx1'))) =>
          var st1 := MState(st.env, st.add, ctx1);
          && EqSeqValue(vs1, vs1')
          && Inv(st1)
          && EqStateWithAdd(st.add, ctx1, ctx1')
          // Additional
          && st1 == st'
          && vs == MSeqValue(vs1, vs1')
        case _ => false
      })
  }

  predicate {:verify false} Pes_Fail(st: S, es: seq<Expr>)
  {
    var ctx := st.ctx;
    var ctx' := ctx.(locals := ctx.locals + st.add);
    var res := InterpExprs(es, st.env, ctx);
    var res' := InterpExprs(es, st.env, ctx');
    Inv(st) ==>
    ExprsValid(st, es) ==>
    res.Failure? && res'.Failure?
  }


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

  function {:verify false} BuildClosureCallState ...
    // Adding this precondition makes the InductAbs proofs easier
    ensures Inv(st) ==> Inv(st')
  {
    var MState(_, add, ctx) := st;
    var ctx' := ctx.(locals := ctx.locals + add);
    var ctx1 := BuildCallState(ctx.locals, vars, argvs.vs);
    var ctx1' := BuildCallState(ctx'.locals, vars, argvs.vs');
    var st' := MState(env, add, ctx1);
    assert Inv(st) ==> Inv(st') by {
      if Inv(st) {
        assume false; // TODO
/*        reveal GEqCtx();
        BuildCallState_EqState(st.ctx.locals, st.ctx'.locals, vars, argvs.vs, argvs.vs');
        assert EqCtx(ctx1.locals, ctx1'.locals);
        assert ctx1.rollback == ctx1'.rollback == map [] by {
          reveal BuildCallState();
        }*/
      }
    }
    st'
  }

  function {:verify false} UpdateState ...
    // Adding this precondition makes the InductUpdate proofs easier
    ensures Inv(st) ==> Inv(st')
  {
    var MState(env, add, ctx) := st;
    var ctx' := ctx.(locals := ctx.locals + add);
    var ctx1 := ctx.(locals := AugmentContext(ctx.locals, vars, vals.vs));
    var ctx1' := ctx'.(locals := AugmentContext(ctx'.locals, vars, vals.vs'));
    var st' := MState(st.env, st.add, ctx1);

    assert Inv(st) ==> Inv(st') by {
      if Inv(st) {
        assume false; // TODO
/*        reveal BuildCallState();
        reveal GEqCtx();
        BuildCallState_EqState(st.ctx.locals, st.ctx'.locals, vars, vals.vs, vals.vs');*/
      }
    }

    st'
  }

  function {:verify false} StateSaveToRollback ...
    // Rem.(SMH): the proofs in which this is used are ignored (see ``ExprValid``)
  {
    var MState(env, add, ctx) := st;
//    var ctx' := ctx.(locals := ctx.locals + add);
    var ctx1 := SaveToRollback(ctx, vars);
    var st' := MState(env, add, ctx1);

    st'
  }

  function {:verify false} StateBindEndScope ...
  {
    var MState(_, _, ctx0) := st0;
    var MState(env, add, ctx) := st;
    var ctx1 := ctx.(locals := CtxBindEndScope(ctx0.locals, ctx.locals, vars));
//    var ctx1' := ctx'.(locals := CtxBindEndScope(ctx0'.locals, ctx'.locals, vars));
    var st' := MState(env, add, ctx1);
    st'
  }

  function {:verify false} StateStartScope ...
    ensures Inv(st) ==> Inv(st')
  {
    var ctx := StartScope(st.ctx);
//    var ctx' := StartScope(st.ctx');
//    reveal GEqCtx();
    var st' := MState(st.env, st.add, ctx);
    assume Inv(st) ==> Inv(st'); // TODO
    st'
  }

  function {:verify false} StateEndScope ...
//    ensures Inv(st0) && Inv(st) && st.outer_rollback == st.outer_rollback' == EmptyCtx ==> Inv(st')
  {
    var ctx := EndScope(st0.ctx, st.ctx);
//    var ctx' := EndScope(st0.ctx', st.ctx');
//    reveal GEqCtx();
    MState(st.env, st.add, ctx)
  }

  function {:verify false} P_Step ... {
    var MState(env, add, ctx) := st;
    var ctx' := ctx.(locals := ctx.locals + add);
    var Return(v, ctx1) := InterpExpr(e, env, ctx).value;
    var Return(v', ctx1') := InterpExpr(e, env, ctx').value;
    (MState(st.env, st.add, ctx1), MValue(v, v'))
  }

  function {:verify false} Pes_Step ... {
    var MState(env, add, ctx) := st;
    var ctx' := ctx.(locals := ctx.locals + add);
    var Return(vs, ctx1) := InterpExprs(es, env, ctx).value;
    var Return(vs', ctx1') := InterpExprs(es, env, ctx').value;
    (MState(st.env, st.add, ctx1), MSeqValue(vs, vs'))
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

  lemma {:verify false} InvImpliesEqStateWithAdd(st: S)
    requires Inv(st)
    ensures
      var MState(env, add, ctx) := st;
      var ctx' := ctx.(locals := ctx.locals + st.add);
      EqStateWithAdd(add, ctx, ctx')
  {
    var MState(env, add, ctx) := st;
    var ctx' := ctx.(locals := ctx.locals + st.add);

    reveal Inv();
    assert EqCtx(ctx.locals, ctx'.locals - add.Keys) by {
      assert ctx'.locals - add.Keys == ctx.locals;
      reveal GEqCtx();
      EqCtx_Refl(ctx.locals);
    }
    assert add.Keys <= ctx'.locals.Keys;
    assert forall x | x in add.Keys :: ctx'.locals[x] == add[x];
    assert ctx.rollback == ctx'.rollback == map [] by { reveal EqStateWithAdd(); }
    reveal EqStateWithAdd();
  }

  lemma {:verify false} InductVar ... {
    reveal InterpExpr();
    var MState(env, add, ctx) := st;
    var ctx' := ctx.(locals := ctx.locals + st.add);
    var v := e.name;
    
    // Start by looking in the local context
    var res0 := TryGetVariable(ctx.locals, v, UnboundVariable(v));
    var res0' := TryGetVariable(ctx'.locals, v, UnboundVariable(v));

    assert add.Keys !! ctx.locals.Keys by { reveal Inv(); }
    assert v !in add.Keys by { reveal ExprValid(); }

    InvImpliesEqStateWithAdd(st);

    if res0.Success? {
      assert res0.Success?;
      assert v in ctx.locals.Keys;
      assert v in ctx'.locals.Keys;
      assert ctx.locals[v] == ctx'.locals[v];
      EqValue_Refl(ctx.locals[v]);
    }
    else {
      // Not in the local context: look in the global context
      assert v in env.globals;
      EqValue_Refl(env.globals[v]);
    }
  }

  lemma {:verify false} InductLiteral ... {
    reveal InterpExpr();
    reveal InterpLiteral();
    if Inv(st) {
      InvImpliesEqStateWithAdd(st);
    }
  }

  lemma {:verify true} BuildCallState_EqAdd(st: S, vars: seq<string>, argvs: VS)
    requires |vars| == |argvs.vs| == |argvs.vs'|
    requires SeqToSet(vars) !! st.add.Keys
    ensures
      var MState(_, add, ctx) := st;
      var ctx' := ctx.(locals := ctx.locals + st.add);
      var ctx1 := BuildCallState(ctx.locals, vars, argvs.vs);
      var ctx1' := BuildCallState(ctx'.locals, vars, argvs.vs');
      // No, this is false: we use m' instead of m
      ctx1' == ctx1.(locals := ctx1.locals + add)
  {
    var MState(_, add, ctx) := st;
    var ctx' := ctx.(locals := ctx.locals + st.add);
//    var ctx1 := BuildCallState(ctx.locals, vars, argvs.vs);
    var ctx1' := BuildCallState(ctx'.locals, vars, argvs.vs');

//    var m := MapOfPairs(Seq.Zip(vars, argvs.vs));
    var m' := MapOfPairs(Seq.Zip(vars, argvs.vs'));
    reveal BuildCallState();
//    assert ctx1.locals == ctx.locals + m;
    assert ctx1'.locals == ctx'.locals + m';

    assert st.add.Keys !! m'.Keys by {
      MapOfPairs_SeqZip_Keys(vars, argvs.vs');
      reveal SeqToSet();
    }
//    assume false;
//    assert (ctx.locals + st.add) + m' == ctx.locals + (st.add + m');
    assert (ctx.locals + st.add) + m' == (ctx.locals + m') + st.add;
    assume false;
  }

  lemma {:verify true} InductAbs ... {
    reveal InterpExpr();
    reveal EqValue_Closure();

    var MState(env, add, ctx) := st;
    var ctx' := ctx.(locals := ctx.locals + st.add);

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

      var res := InterpCallFunctionBody(cv, env, argvs.vs);
      var res' := InterpCallFunctionBody(cv', env, argvs.vs');

      var ctx1 := BuildCallState(cv.ctx, vars, argvs.vs);
      var ctx1' := BuildCallState(cv'.ctx, cv'.vars, argvs.vs');

//      var m := MapOfPairs(Seq.Zip(vars, argvs.vs));
//      var m' := MapOfPairs(Seq.Zip(vars, argvs.vs'));
//      reveal BuildCallState();
//      assert ctx1.locals == ctx.locals + m;
//      assert ctx1'.locals == ctx'.locals + m';

      var st1 := BuildClosureCallState(st, vars, body, env, argvs);

//      assert 
      assert ctx1' == ctx1.(locals := ctx1.locals + add) by {
        // TODO: this is false: we have: ctx1'.locals == ctx.locals + m' + add
        // (and m' != m)
        // This will probably not work with the invariant, that we should update?...
        // Also, maybe:
        // MState(env, ctx, ctx', add) where ctx ~= ctx'
        assert SeqToSet(vars) !! st.add.Keys by {
          reveal SeqToSet();
          reveal ExprValid();
        }
        BuildCallState_EqAdd(st, vars, argvs);
      }
      assert Inv(st1);
      assert st1 == MState(env, add, ctx1);
      assert P(st1, body);
      
      var res2 := InterpExpr(cv.body, env, ctx1);
      var res2' := InterpExpr(cv'.body, env, ctx1');

      reveal InterpCallFunctionBody();

      assert Inv(st1);
      assume ExprValid(st1, body); // TODO

      if res2.Success? {
        var Return(val, ctx2) := res2.value;
        var Return(val', ctx2') := res2'.value;
      }
      else {
        assert res.Failure?;
      }
    }

    InvImpliesEqStateWithAdd(st);
    assert EqValue_Closure(cv, cv');
  }

  lemma {:verify false} InductAbs_CallState ... {
    reveal InterpExpr();
    reveal InterpCallFunctionBody();
    reveal BuildCallState();
  }

  lemma {:verify false} InductExprs_Nil ... {
    assume false; // TODO
    reveal InterpExprs(); }
  lemma {:verify false} InductExprs_Cons ... {
    assume false; // TODO
    reveal InterpExprs(); }

  lemma {:verify false} InductApplyLazy_Fail ... {
    assume false; // TODO
    reveal InterpExpr(); }
  lemma {:verify false} InductApplyLazy_Succ ... {
    assume false; // TODO
    reveal InterpExpr(); }

  lemma {:verify false} InductApplyEager_Fail ... {
    assume false; // TODO
  }

  lemma {:verify false} InductApplyEagerUnaryOp_Succ ... {
    assume false; // TODO
  }

  lemma {:verify false} InductApplyEagerBinaryOp_Succ ... {
    assume false; // TODO
    reveal InterpExpr();
//    InterpBinaryOp_Eq(e, e, op, v0.v, v1.v, v0.v', v1.v');
  }

  lemma {:verify false} {:fuel SeqVToVS, 2} InductApplyEagerTernaryOp_Succ ... {
    assume false; // TODO
    reveal InterpExpr();
    // TODO(SMH): ``SeqVToVS`` is called on literals: we shouldn't need fuel 2
//    assert SeqVToVS([v0, v1, v2]) == MSeqValue([v0.v, v1.v, v2.v], [v0.v', v1.v', v2.v']);
//    InterpTernaryOp_Eq(e, e, op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');
  }

  lemma {:verify false} InductApplyEagerBuiltinDisplay ... {
    assume false; // TODO
    reveal InterpExpr();
//    Interp_Apply_Display_EqValue(e, e, ty.kind, argvs.vs, argvs.vs');
  }

  lemma {:verify false} InductApplyEagerFunctionCall ... {
    assume false; // TODO
    reveal InterpExpr();
//    InterpFunctionCall_EqState(e, e, st.env, fv.v, fv.v', argvs.vs, argvs.vs');
  }

  lemma {:verify false} InductIf_Fail ... {
    assume false; // TODO
    reveal InterpExpr(); }
  lemma {:verify false} InductIf_Succ ... {
    assume false; // TODO
    reveal InterpExpr(); }

  lemma {:verify false} InductUpdate_Fail ... {
    assume false; // TODO
    reveal InterpExpr(); }
  lemma {:verify false} InductUpdate_Succ ... {
    assume false; // TODO
    reveal InterpExpr(); }

  lemma {:verify false} InductVarDecl_None_Succ ... {
    assume false; // TODO
    reveal InterpExpr(); }
  lemma {:verify false} InductVarDecl_Some_Fail ... {
    assume false; // TODO
    reveal InterpExpr(); }
  lemma {:verify false} InductVarDecl_Some_Succ  ... {
    assume false; // TODO
    reveal InterpExpr(); }

  lemma {:verify false} InductBind_Fail ... {
    assume false; // TODO
    reveal InterpExpr(); }
  lemma {:verify false} InductBind_Succ ... {
    assume false; // TODO
    reveal InterpExpr();

    // Sanity check: there are issues in ``EqInterpScopes``
/*    var MState(env, _, ctx, _, ctx') := st;
    assert InterpExpr(e, env, ctx) == Success(Return(v.v, st4.ctx));
    assert InterpExpr(e, env, ctx') == Success(Return(v.v', st4.ctx'));

    reveal GEqCtx();*/
  }

  // TODO(SMH): I tried simplifying the proofs below by adding a `requires` in ``InductBlock_Fail``
  // and ``InductBlock_Succ`` to provide the result of calling ``InterpExprs_Block_Equiv_Strong``,
  // but it didn't work due to SMT solvers' misteries.
  lemma {:verify false} InductBlock_Fail ...
  {
    assume false; // TODO
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
//    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
//    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx');
  }

  lemma {:verify false} InductBlock_Succ ...
  {
    assume false; // TODO
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
//    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
//    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx');
  }
}


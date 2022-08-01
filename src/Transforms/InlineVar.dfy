//include "../Interop/CSharpDafnyASTModel.dfy"
//include "../Interop/CSharpInterop.dfy"
//include "../Interop/CSharpDafnyInterop.dfy"
//include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Semantics/ExprInduction.dfy"
include "../Semantics/Pure.dfy"
//include "InterpStateIneq.dfy"

module Bootstrap.Transforms.InlineVar.Base {
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

  function method {:opaque} SeqToSet<T>(s: seq<T>): set<T>
    // Unfortunately, we need this small opaque helper to prevent with proof explosions.
  {
    set x | x in s
  }

  function method {:opaque} VarsToNameSet(vars: seq<Exprs.Var>): set<string>
    // Same as for ``SeqToSet``: making this definition opaque is annoying, but we need it to
    // prevent proof explosions.
  {
    set x | x in vars :: x.name
  }

  // TODO(SMH): move?
  function method {:verify false} VarsOfExpr(e: Expr): set<string>
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
        s + VarsToNameSet(vdecls)
      case Update(vars, vals) =>
        (set x | x in vars) + VarsOfExprs(vals)
      case Bind(vars, vals, body) =>
        VarsToNameSet(vars) + VarsOfExprs(vals) + VarsOfExpr(body)
      case If(cond, thn, els) =>
        VarsOfExpr(cond) + VarsOfExpr(thn) + VarsOfExpr(els)
    }
  }

  function method {:verify false} VarsOfExprs(es: seq<Expr>): set<string>
    decreases Expr.Exprs_Size(es), 1
  {
    if es == [] then {}
    else VarsOfExpr(es[0]) + VarsOfExprs(es[1..])
  }

  datatype {:verify false} Acc = Acc(subst: map<string, Expr>, frozen: set<string>)
  const {:verify false} EmptyBlock: Interp.Expr := reveal Interp.SupportsInterp(); Expr.Block([])

  predicate method {:verify false} CanUpdateVars(vars: set<string>, frozen: set<string>)
  {
    vars !! frozen
  }

  predicate method {:verify false} CanInlineVar(p: (Exprs.Var, Expr) -> bool, v: Exprs.Var, rhs: Expr)
  {
    && p(v, rhs) // The filtering predicate allows to inline this variable
    && IsPure(rhs) // The rhs is pure - TODO: write a more general, less constraining purity check
  }

  function method {:verify false} AddToAcc(acc: Acc, v: Exprs.Var, rhs: Expr): Acc
    // Register a substitution: variable -> rhs.
    //
    // We freeze the variable itself, and all the variables appearing in the rhs.
  {
    var subst := acc.subst[v.name := rhs];
    var frozen := acc.frozen + {v.name} + VarsOfExpr(rhs); // We don't necessarily need to freeze `v.name`
    Acc(subst, frozen)
  }
  
  function method {:verify false} InlineInExpr(p: (Exprs.Var, Expr) -> bool, acc: Acc, e: Expr):
    Result<(Acc, Expr), ()>
    decreases e.Size(), 0
    // An older version of ``InlineExpr`` took as input the set of variables updated by the
    // expressions to be evaluated *after* the current one: this allowed to preemptively check
    // if it was legal to inline a variable. However, we couldn't prove that this version is
    // correct by using the induction principle, because there was no way to properly use it
    // to thread the `after` parameter which was computed in a backwards manner (note that
    // it would have been possible by leveraging universal quantifiers, but this ususally leads
    // to prove explosion and unstability).
    // It would be good to be able to prove this version correct, because it allows to check if
    // it is valid to inline a variable (and doesn't inline it if it is not), while the current
    // version preemptively inlines then fails if it was actually not valid to do so.
    //
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
        if v in acc.subst.Keys then Success((acc, acc.subst[v])) else Success((acc, e))

      case Literal(_) => Success((acc, e))

      case Abs(vars, body) =>
        :- Need(CanUpdateVars(SeqToSet(vars), acc.frozen), ());
        var (_, body') :- InlineInExpr(p, acc, body);
        Success((acc, e.(body := body')))

      case Apply(aop, args) =>
        var (acc', args') :- InlineInExprs(p, acc, args);
        Success((acc', e.(args := args')))

      case Block(stmts) =>
        var (_, stmts') :- InlineInExprs(p, acc, stmts);
        // We use the original acc because there is a scope
        Success((acc, e.(stmts := stmts')))

      case VarDecl(vdecls, ovals) =>
        :- Need(CanUpdateVars(VarsToNameSet(vdecls), acc.frozen), ());
        if ovals.Some? then
          var (acc1, vals') :- InlineInExprs(p, acc, ovals.value);
          // For now, we try to inline only if there is exactly one variable
          if |vdecls| == 1 && CanInlineVar(p, vdecls[0], vals'[0]) then
            var acc2 := AddToAcc(acc, vdecls[0], vals'[0]);
            Success((acc2, EmptyBlock))
          else Success((acc1, Expr.VarDecl(vdecls, Exprs.Some(vals'))))
        else Success((acc, e))

      case Update(vars, vals) =>
        :- Need(CanUpdateVars(set x | x in vars, acc.frozen), ());
        var (acc', vals') :- InlineInExprs(p, acc, vals);
        Success((acc', e.(vals := vals')))

      case Bind(bvars, bvals, bbody) =>
        :- Need(CanUpdateVars(VarsToNameSet(bvars), acc.frozen), ()); // Not necessary, but let's make thinkgs simple for now
        var (acc1, bvals') :- InlineInExprs(p, acc, bvals);
        // For now, we try to inline only if there is exactly one variable
        // Rk.: we return the original acc because there is a scope
        if |bvars| == 1 && CanInlineVar(p, bvars[0], bvals'[0]) then
            var acc2 := AddToAcc(acc, bvars[0], bvals'[0]);
            var (_, bbody') :- InlineInExpr(p, acc2, bbody);
            Success((acc, Expr.Block([bbody'])))
        else
          var (acc2, bbody') :- InlineInExpr(p, acc1, bbody);
          Success((acc, Expr.Bind(bvars, bvals', bbody')))

      case If(cond, thn, els) =>
        var (acc1, cond') :- InlineInExpr(p, acc, cond);
        var (acc2, thn') :- InlineInExpr(p, acc1, thn);
        var (acc2', els') :- InlineInExpr(p, acc1, els);
        // The branches must agree - actually they should contain blocks, so they shouldn't leak any variables
        :- Need(acc2 == acc2', ());
        Success((acc2, Expr.If(cond', thn', els')))
    }
  }

  function method {:verify false} InlineInExprs(p: (Exprs.Var, Expr) -> bool, acc: Acc, es: seq<Expr>) :
    (out: Result<(Acc, seq<Expr>), ()>)
    decreases Expr.Exprs_Size(es), 1
    ensures
      match out {
        case Success((_, es')) => |es'| == |es|
        case Failure(_) => true
      }
  {
    if es == [] then Success((acc, []))
    else
      var (acc1, e') :- InlineInExpr(p, acc, es[0]);
      var (acc2, es') :- InlineInExprs(p, acc1, es[1..]);
      Success((acc2, [e'] + es'))
  }
}

module Bootstrap.Transforms.InlineVar.BaseProofs refines Semantics.ExprInduction {
  // TODO: remove //
/*  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import opened Semantics.Interp
  import opened Semantics.Values
  import opened Semantics.Equiv
  import opened Utils.Lib.Datatypes
  type {:verify false} Expr = Interp.Expr*/
  // END of TODO: remove //

/*  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import Semantics.Interp
  import opened Semantics.Equiv
  import opened Generic
  import Shallow*/
  import opened Base

  type {:verify false} Value = Interp.Value
  type {:verify false} Context = Interp.Context
//  const {:verify false} VarsToNames := Interp.VarsToNames

  const {:verify false} p: (Exprs.Var, Expr) -> bool

//  const EmptyCtx: Context := map[]

  // - `ctx`: the environment to execute the original expression
  // - `ctx'`: the environment to execute the expression on which we performed inlinings
  datatype {:verify false} MState = MState(env: Environment, acc: Acc, ctx: State, ctx': State)
  datatype {:verify false} MValue = MValue(v: Value, v': Value)
  datatype {:verify false} MSeqValue = MSeqValue(vs: seq<Value>, vs': seq<Value>)

/*  predicate EqOuterRollback(outer_rollback: Context, ctx: State, outer_rollback': Context, ctx': State)
  {
    EqCtx(ctx.rollback + outer_rollback, ctx'.rollback + outer_rollback')
  }*/

/*
  // TODO(SMH): move?
  predicate {:verify false} {:opaque} EqSubCtx(keys: set<string>, ctx: Context, ctx': Context)
  {
    && keys <= ctx.Keys
    && keys <= ctx'.Keys
    && forall x | x in keys :: EqValue(ctx[x], ctx'[x])
  }

  // TODO(SMH): move? This is not used in this module. But this should be kept with ``EqOuterRollback``
  predicate {:verify false} EqRolled(keys: set<string>, ctx: State, ctx': State)
  {
    EqSubCtx(keys, ctx.locals + ctx.rollback, ctx'.locals + ctx'.rollback)
  }*/

  predicate {:verify false} {:opaque} EqStateOnAcc(env: Environment, acc: Acc, ctx: State, ctx': State)
    requires acc.subst.Keys <= ctx.locals.Keys
  {
    && acc.subst.Keys <= acc.frozen
    && (forall x | x in acc.subst.Keys :: VarsOfExpr(acc.subst[x]) <= acc.frozen)
    && (forall x | x in acc.subst.Keys ::
       var res := InterpExpr(acc.subst[x], env, ctx');
       match res {
         case Success(Return(v, ctx'')) =>
           && ctx'' == ctx'
           && v == ctx.locals[x]
         case Failure(_) => false
       })
  }

  predicate {:verify false} EqStateWithAcc_Locals(env: Environment, acc: Acc, ctx: State, ctx': State)
    // Auxiliary definition we use for ``EqStateWithAcc``.
    //
    // This definition contains all the conditions pertaining to the `locals` contexts (i.e., without
    // the `rollback`).
  {
    && ctx'.locals.Keys !! acc.subst.Keys
    && ctx'.locals.Keys + acc.subst.Keys == ctx.locals.Keys
    && EqCtx(map x | x in ctx'.locals.Keys :: ctx.locals[x], ctx'.locals)
    && EqStateOnAcc(env, acc, ctx, ctx')
  }


  predicate {:verify false} {:opaque} EqStateWithAcc(env: Environment, acc: Acc, ctx: State, ctx': State)
    // Predicate stating the conditions under which two states are equivalent under the presence of
    // an inlining accumulator.
  {
    && EqStateWithAcc_Locals(env, acc, ctx, ctx')
    && ctx'.rollback.Keys <= ctx.rollback.Keys
    && ctx.rollback.Keys <= ctx'.rollback.Keys + acc.subst.Keys
    && EqCtx(map x | x in ctx'.rollback.Keys :: ctx.rollback[x], ctx'.rollback)
  }

  predicate {:verify false} Inv(st: MState)
  {
    EqStateWithAcc(st.env, st.acc, st.ctx, st.ctx')
  }

  predicate {:verify false} {:opaque} StateRel(st: MState, st': MState)
  {
    && st.acc.subst.Keys <= st'.acc.subst.Keys
    && forall x | x in st.acc.subst.Keys :: st'.acc.subst[x] == st.acc.subst[x]
//    && st.env == st'.env
  }

  lemma {:verify false} StateRel_Trans(st0: MState, st1: MState, st2: MState)
    requires StateRel(st0, st1)
    requires StateRel(st1, st2)
    ensures StateRel(st0, st2)
  {
    reveal StateRel();
    reveal StateRel();
  }

/*
  predicate {:verify false} EqResult<V>(eq_value: (V,V) -> bool, subst: Subst, res: InterpResult<V>, res': InterpResult<V>)
  {
    match (res, res')
      case (Success(Return(v, ctx)), Success(Return(v', ctx'))) =>
        && eq_value(v, v')
        && EqCtx(ctx.locals, ctx'.locals)
        && EqOuterRollback(outer_rollback, ctx, outer_rollback', ctx')
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
  }


  predicate {:verify false} Inv(st: MState)
  {
    && EqCtx(st.ctx.locals, st.ctx'.locals)
    && EqOuterRollback(st.outer_rollback, st.ctx, st.outer_rollback', st.ctx')
  }*/

  type {:verify false} S(!new) = MState
  type {:verify false} V(!new) = MValue
  type {:verify false} VS(!new) = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

  predicate {:verify false} P(st: S, e: Expr)
  {
    var res := InterpExpr(e, st.env, st.ctx);
    var res' := InterpExpr(e, st.env, st.ctx');
    Inv(st) ==>
    InlineInExpr(p, st.acc, e).Success? ==>
    match (res, res') {
      case (Success(Return(v1, ctx1)), Success(Return(v1', ctx1'))) =>
        var (acc1, _) := InlineInExpr(p, st.acc, e).value;
        var st1 := MState(st.env, acc1, ctx1, ctx1');
        && EqValue(v1, v1')
        && Inv(st1)
        && StateRel(st, st1)
      case (Failure(_), _) => true
      case _ => false
    }
  }
  
  predicate {:verify false} P_Succ(st: S, e: Expr, st': S, v: V)
  {
    var res := InterpExpr(e, st.env, st.ctx);
    var res' := InterpExpr(e, st.env, st.ctx');
    && Inv(st)
    && InlineInExpr(p, st.acc, e).Success?
    && match (res, res') {
      case (Success(Return(v1, ctx1)), Success(Return(v1', ctx1'))) =>
        var (acc1, _) := InlineInExpr(p, st.acc, e).value;
        var st1 := MState(st.env, acc1, ctx1, ctx1');
        && EqValue(v1, v1')
        && Inv(st1)
        && StateRel(st, st1)
        // Additional
        && st1 == st'
        && v == MValue(v1, v1')
      case _ => false
    }
  }

  predicate {:verify false} P_Fail(st: S, e: Expr)
  {
    Inv(st) ==> InlineInExpr(p, st.acc, e).Success? ==> InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate {:verify false} Pes(st: S, es: seq<Expr>)
  {
    var res := InterpExprs(es, st.env, st.ctx);
    var res' := InterpExprs(es, st.env, st.ctx');
    Inv(st) ==>
    InlineInExprs(p, st.acc, es).Success? ==>
    match (res, res') {
      case (Success(Return(vs1, ctx1)), Success(Return(vs1', ctx1'))) =>
        var (acc1, _) := InlineInExprs(p, st.acc, es).value;
        var st1 := MState(st.env, acc1, ctx1, ctx1');
        && EqSeqValue(vs1, vs1')
        && Inv(st1)
        && StateRel(st, st1)
      case (Failure(_), _) => true
      case _ => false
    }
  }

  predicate {:verify false} Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
  {
    var res := InterpExprs(es, st.env, st.ctx);
    var res' := InterpExprs(es, st.env, st.ctx');
    && Inv(st)
    && InlineInExprs(p, st.acc, es).Success?
    && match (res, res') {
      case (Success(Return(vs1, ctx1)), Success(Return(vs1', ctx1'))) =>
        var (acc1, _) := InlineInExprs(p, st.acc, es).value;
        var st1 := MState(st.env, acc1, ctx1, ctx1');
        && EqSeqValue(vs1, vs1')
        && Inv(st1)
        && StateRel(st, st1)
        // Additional
        && st1 == st'
        && vs == MSeqValue(vs1, vs1')
      case _ => false
    }
  }

  predicate {:verify false} Pes_Fail(st: S, es: seq<Expr>)
  {
    Inv(st) ==> InlineInExprs(p, st.acc, es).Success? ==> InterpExprs(es, st.env, st.ctx).Failure?
  }

  function {:verify false} AppendValue ...
  {
    MSeqValue([v.v] + vs.vs, [v.v'] + vs.vs')
  }

  function {:verify false} SeqVToVS ...
  {
    if vs == [] then MSeqValue([], [])
    else
      AppendValue(MValue(vs[0].v, vs[0].v'), SeqVToVS(vs[1..]))
  }
  
  function {:verify false} GetNilVS ...
  {
    MSeqValue([], [])
  }

  ghost const {:verify false} UnitV := MValue(Values.Unit, Values.Unit)

  function {:verify false} VS_Last ...
  {
    var v := vs.vs[|vs.vs| - 1];
    var v' := vs.vs'[|vs.vs| - 1];
    MValue(v, v')
  }

  predicate {:verify false} VS_UpdateStatePre ...
  {
    && |argvs.vs| == |argvs.vs'| == |vars|
    && forall i | 0 <= i < |argvs.vs| :: EqValue(argvs.vs[i], argvs.vs'[i])
  }

  lemma {:verify false} BuildClosure_UpdateState_Inv(
    acc: Acc, env: Environment, ctx: State, ctx': State, env': Environment, ctx1: State, ctx1': State,
    vars: seq<string>, vals: VS)
    requires Inv(MState(env, acc, ctx, ctx'))
    requires CanUpdateVars(SeqToSet(vars), acc.frozen)
    requires VS_UpdateStatePre(MState(env, acc, ctx, ctx'), vars, vals)
    requires ctx1.locals == AugmentContext(ctx.locals, vars, vals.vs);
    requires ctx1'.locals == AugmentContext(ctx'.locals, vars, vals.vs');
    ensures EqStateWithAcc_Locals(env', acc, ctx1, ctx1')
  {
    MapOfPairs_SeqZip_EqCtx(vars, vals.vs, vals.vs');
    var nbinds := MapOfPairs(Seq.Zip(vars, vals.vs));
    var nbinds' := MapOfPairs(Seq.Zip(vars, vals.vs'));

    reveal BuildCallState();
    assert ctx1.locals == ctx.locals + nbinds;
    assert ctx1'.locals == ctx'.locals + nbinds';
    assert nbinds.Keys == nbinds'.Keys by { reveal GEqCtx(); }

    // This is true because the new bindings are disjoint from acc.subst
    assert ctx1'.locals.Keys !! acc.subst.Keys by {
      assert ctx'.locals.Keys !! acc.subst.Keys by { reveal EqStateWithAcc(); }
      assert nbinds.Keys !! acc.subst.Keys by {
        MapOfPairs_SeqZip_Keys(vars, vals.vs);
        assert nbinds.Keys == set x | x in vars;
        assert acc.subst.Keys <= acc.frozen by { reveal EqStateWithAcc(); reveal EqStateOnAcc(); }
        // The following assert is given by ``CanUpdateVars``
        assert (set x | x in vars) !! acc.frozen by { reveal SeqToSet(); }
      }
    }

    // This is true because the new bindings are the same on the two sides:
    assert ctx1'.locals.Keys + acc.subst.Keys == ctx1.locals.Keys by { reveal EqStateWithAcc(); }

    assert EqCtx(map x | x in ctx1'.locals.Keys :: ctx1.locals[x], ctx1'.locals) by {
      // TODO: lemma:
      // - if binding not updated, then ok
      // - if binding updated: ok
      var locals1 := map x | x in ctx1'.locals.Keys :: ctx1.locals[x];
      var locals1' := ctx1'.locals;
      assert locals1.Keys == locals1'.Keys;
      forall x | x in locals1'.Keys ensures EqValue(locals1[x], locals1'[x]) {
        assume false;
      }
      reveal GEqCtx();
    }

    assert EqStateOnAcc(env', acc, ctx1, ctx1') by {
      assert acc.subst.Keys <= acc.frozen by { reveal EqStateWithAcc(); reveal EqStateOnAcc(); } // Ok
      assert (forall x | x in acc.subst.Keys :: VarsOfExpr(acc.subst[x]) <= acc.frozen) by { reveal EqStateWithAcc(); reveal EqStateOnAcc(); }
      assume ( // TODO: general lemma: adding bindings which are not used leads to same interp
        // TODO: we may have a problem with the environment
        forall x | x in acc.subst.Keys ::
        var res := InterpExpr(acc.subst[x], env', ctx1');
        match res {
          case Success(Return(v, ctx1'')) =>
            && ctx1'' == ctx1'
            && v == ctx1.locals[x]
          case Failure(_) => false
        });
        reveal EqStateOnAcc();
    }

    assert EqStateWithAcc_Locals(env', acc, ctx1, ctx1');
  }

  function {:verify false} BuildClosureCallState ...
    // Adding this postcondition makes the InductAbs proofs easier
    ensures Inv(st) && CanUpdateVars(SeqToSet(vars), st.acc.frozen) ==> Inv(st') && StateRel(st, st')
  {
    var acc := st.acc;
    var ctx := st.ctx;
    var ctx' := st.ctx';
    var ctx1 := BuildCallState(st.ctx.locals, vars, argvs.vs);
    var ctx1' := BuildCallState(st.ctx'.locals, vars, argvs.vs');
    var st' := MState(env, acc, ctx1, ctx1');

    var b := Inv(st) && CanUpdateVars(SeqToSet(vars), st.acc.frozen);
    assert b ==> Inv(st') && StateRel(st, st') by {
      if b {
        MapOfPairs_SeqZip_EqCtx(vars, argvs.vs, argvs.vs');
        var nbinds := MapOfPairs(Seq.Zip(vars, argvs.vs));
        var nbinds' := MapOfPairs(Seq.Zip(vars, argvs.vs'));

        reveal BuildCallState();
        assert ctx1 == State(locals := ctx.locals + nbinds);
        assert ctx1' == State(locals := ctx'.locals + nbinds');
        assert nbinds.Keys == nbinds'.Keys by { reveal GEqCtx(); }

        assert Inv(st') by {
          // The rollback invariants are trivial because the rollbacks are empty on both sides
          assert ctx1'.rollback.Keys <= ctx1.rollback.Keys; // Ok
          assert ctx1.rollback.Keys <= ctx1'.rollback.Keys + acc.subst.Keys; // Ok
          assert EqCtx(map x | x in ctx1'.rollback.Keys :: ctx1.rollback[x], ctx1'.rollback) by { reveal GEqCtx(); } // Ok

          // Prove the remaining conditions of the invariant
          BuildClosure_UpdateState_Inv(acc, st.env, ctx, ctx', env, ctx1, ctx1', vars, argvs);
          reveal EqStateWithAcc();
        }

        // The two states are trivially related because the accumulator is unchanged
        assert StateRel(st, st') by { reveal StateRel(); }
      }
    }
    st'
  }

  function {:verify false} UpdateState ...
    // Adding this postcondition makes the InductUpdate proofs easier
    ensures Inv(st) && CanUpdateVars(SeqToSet(vars), st.acc.frozen) ==> Inv(st') && StateRel(st, st')
  {
    var acc := st.acc;
    var ctx := st.ctx;
    var ctx' := st.ctx';
    var ctx1 := st.ctx.(locals := AugmentContext(st.ctx.locals, vars, vals.vs));
    var ctx1' := st.ctx'.(locals := AugmentContext(st.ctx'.locals, vars, vals.vs'));
    var st' := MState(st.env, st.acc, ctx1, ctx1'); // TODO: st.acc

    var b := Inv(st) && CanUpdateVars(SeqToSet(vars), st.acc.frozen);
    assert b ==> Inv(st') && StateRel(st, st') by {
      if b {
        MapOfPairs_SeqZip_EqCtx(vars, vals.vs, vals.vs');
        var nbinds := MapOfPairs(Seq.Zip(vars, vals.vs));
        var nbinds' := MapOfPairs(Seq.Zip(vars, vals.vs'));

        reveal BuildCallState();
        assert ctx1.locals == ctx.locals + nbinds;
        assert ctx1'.locals == ctx'.locals + nbinds';
        assert nbinds.Keys == nbinds'.Keys by { reveal GEqCtx(); }

        assert Inv(st') by {
          assert ctx1'.rollback.Keys <= ctx1.rollback.Keys by { reveal EqStateWithAcc(); } // Ok
          assert ctx1.rollback.Keys <= ctx1'.rollback.Keys + acc.subst.Keys by { reveal EqStateWithAcc(); } // Ok
          assert EqCtx(map x | x in ctx1'.rollback.Keys :: ctx1.rollback[x], ctx1'.rollback) by { reveal EqStateWithAcc(); } // Ok

          // Prove the remaining conditions of the invariant
          BuildClosure_UpdateState_Inv(acc, st.env, ctx, ctx', st.env, ctx1, ctx1', vars, vals);
          reveal EqStateWithAcc();
        }

        // The two states are trivially related because the accumulator is unchanged
        assert StateRel(st, st') by { reveal StateRel(); }
      }
    }
    st'
  }

  function {:verify false} StateSaveToRollback_Inline(st: S, vars: seq<string>): (st':S)
  {
    // TODO
    st
  }

  function {:verify false} StateSaveToRollback_NoInline(st: S, vdecls: seq<Exprs.Var>, rhs': seq<Expr>): (st':S)
    requires |rhs'| == |vdecls|
    requires !(|vdecls| == 1 && CanInlineVar(p, vdecls[0], rhs'[0]))
    ensures Inv(st) && CanUpdateVars(SeqToSet(VarsToNames(vdecls)), st.acc.frozen) ==> Inv(st') && StateRel(st, st')
  {
    var MState(env, acc, ctx, ctx') := st;
    var vars := VarsToNames(vdecls);
    var ctx1 := SaveToRollback(st.ctx, vars);
    var ctx1' := SaveToRollback(st.ctx', vars);
    var st' := MState(st.env, acc, ctx1, ctx1');

    var b := Inv(st) && CanUpdateVars(SeqToSet(vars), st.acc.frozen);
    assert b ==> Inv(st') && StateRel(st, st') by {
      if b {
        assume false;
      }
    }

    st'
  }

  // TODO(SMH): we need the rhs (not only the variables) as input parameters + some length conditions.
  // Actually it doesn't work: we need to prevent the UpdateState which happens afterward in the case
  // where we inline the rhs.
  function {:verify false} StateSaveToRollback ...
    ensures Inv(st) ==> Inv(st')
  {
    assume false; // TODO
    var MState(env, acc, ctx, ctx') := st;
    var ctx1 := SaveToRollback(st.ctx, vars);
    var ctx1' := SaveToRollback(st.ctx', vars);
    var st' := MState(st.env, acc, ctx1, ctx1'); // TODO: acc

    assert Inv(st) ==> Inv(st') by {
      /*
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
      }*/
    }

    st'
  }

  function {:verify false} StateStartScope ...
    ensures Inv(st) ==> Inv(st') && StateRel(st, st')
  {
    var MState(env, acc, ctx, ctx') := st;
    var ctx1 := StartScope(ctx);
    var ctx1' := StartScope(ctx');
    var st' := MState(env, acc, ctx1, ctx1');
    var b := Inv(st);
    assert b ==> Inv(st') && StateRel(st, st') by {
      if b {
        assert EqStateWithAcc(env, acc, ctx1, ctx1') by {
          assert EqStateWithAcc_Locals(env, acc, ctx1, ctx1') by {
            assert ctx1'.locals.Keys !! acc.subst.Keys by { reveal EqStateWithAcc(); }
            assert ctx1'.locals.Keys + acc.subst.Keys == ctx1.locals.Keys by { reveal EqStateWithAcc(); }
            assert EqCtx(map x | x in ctx1'.locals.Keys :: ctx1.locals[x], ctx1'.locals) by { reveal EqStateWithAcc(); }
            assert EqStateOnAcc(env, acc, ctx1, ctx1') by {
              assert acc.subst.Keys <= acc.frozen by { reveal EqStateWithAcc(); reveal EqStateOnAcc(); }
              assert forall x | x in acc.subst.Keys :: VarsOfExpr(acc.subst[x]) <= acc.frozen by { reveal EqStateWithAcc(); reveal EqStateOnAcc(); }

              // TODO: we need this to hold whatever the *rollback* (which we just initialized to empty).
              // It should be ok because we should not need to use it: we can't close a scope without
              // opening one before.
              // TODO: should be a different lemma than the one for BuildClosureCallState (it shouldn't
              // need to be recursive actually: for the recursive cases like Block, we just need the
              // reflexivity of EqInterp).
              assume forall x | x in acc.subst.Keys ::
                 var res := InterpExpr(acc.subst[x], env, ctx1');
                 match res {
                   case Success(Return(v, ctx1'')) =>
                     && ctx1'' == ctx1'
                     && v == ctx1.locals[x]
                   case Failure(_) => false
                 };
              reveal EqStateOnAcc();
            }
          }
          assert ctx1'.rollback.Keys <= ctx1.rollback.Keys;
          assert ctx1.rollback.Keys <= ctx1'.rollback.Keys + acc.subst.Keys;
          assert EqCtx(map x | x in ctx1'.rollback.Keys :: ctx1.rollback[x], ctx1'.rollback) by { reveal GEqCtx(); }
          reveal EqStateWithAcc();
        }
        assert StateRel(st, st') by { reveal StateRel(); }
      }
    }
//    reveal GEqCtx();
    st'
  }

  function {:verify false} StateEndScope ...
    ensures Inv(st0) && Inv(st) ==> Inv(st') && StateRel(st0, st')
  {
    var MState(env, acc, ctx0, ctx0') := st0;
    var ctx1 := EndScope(st0.ctx, st.ctx);
    var ctx1' := EndScope(st0.ctx', st.ctx');
    var st' := MState(env, acc, ctx1, ctx1');
    var b := Inv(st0) && Inv(st);
    assert b ==> Inv(st') && StateRel(st0, st') by {
      if b {
        assert EqStateWithAcc(env, acc, ctx1, ctx1') by {
          assert EqStateWithAcc_Locals(env, acc, ctx1, ctx1') by {
            assert ctx1'.locals.Keys !! acc.subst.Keys by { reveal EqStateWithAcc(); }
            assert ctx1'.locals.Keys + acc.subst.Keys == ctx1.locals.Keys by {
              // TODO: we need more contextual information to prove those two assumptions (we can't
              // call InterpStateIneq in the current state). Move those as assumptions, and call
              // InterpEqStateIneq wherever needed in the other lemmas?
              assume ctx0.locals.Keys <= st.ctx.locals.Keys + st.ctx.rollback.Keys; // TODO
              assume ctx0'.locals.Keys <= st.ctx'.locals.Keys + st.ctx'.rollback.Keys; // TODO
              reveal EqStateWithAcc();
            }
            assert EqCtx(map x | x in ctx1'.locals.Keys :: ctx1.locals[x], ctx1'.locals) by {
              reveal EqStateWithAcc();
              reveal GEqCtx();
            }
            assert EqStateOnAcc(env, acc, ctx1, ctx1') by {
              assert acc.subst.Keys <= acc.frozen by { reveal EqStateWithAcc(); reveal EqStateOnAcc(); }
              assert forall x | x in acc.subst.Keys :: VarsOfExpr(acc.subst[x]) <= acc.frozen by { reveal EqStateWithAcc(); reveal EqStateOnAcc(); }

              // TODO: lemma:
              // - prove that the locals used in the substs are left unchanged (left unchanged
              //   in locals, don't appear in rollback)
              // - under those assumptions, prove that evaluating the expressions is the same
              //   (same lemma as for ``BuildClosure_UpdateState_Inv``)
              assume forall x | x in acc.subst.Keys ::
                 var res := InterpExpr(acc.subst[x], env, ctx1');
                 match res {
                   case Success(Return(v, ctx1'')) =>
                     && ctx1'' == ctx1'
                     && v == ctx1.locals[x]
                   case Failure(_) => false
                 };
              reveal EqStateOnAcc();
            }
          }
          assert ctx1'.rollback.Keys <= ctx1.rollback.Keys by { reveal EqStateWithAcc(); }
          assert ctx1.rollback.Keys <= ctx1'.rollback.Keys + acc.subst.Keys by { reveal EqStateWithAcc(); }
          assert EqCtx(map x | x in ctx1'.rollback.Keys :: ctx1.rollback[x], ctx1'.rollback) by { reveal EqStateWithAcc(); }
          reveal EqStateWithAcc();
        }
        assert StateRel(st0, st') by { reveal StateRel(); }
      }
    }
    st'
  }

  function {:verify false} P_Step ...
  {
    var Return(v1, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    var Return(v1', ctx1') := InterpExpr(e, st.env, st.ctx').value;
    var (acc1, _) := InlineInExpr(p, st.acc, e).value;
    (MState(st.env, acc1, ctx1, ctx1'), MValue(v1, v1'))
  }

  function {:verify false} Pes_Step ...
  {
    var Return(vs1, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    var Return(vs1', ctx1') := InterpExprs(es, st.env, st.ctx').value;
    var (acc1, _) := InlineInExprs(p, st.acc, es).value;
    (MState(st.env, acc1, ctx1, ctx1'), MSeqValue(vs1, vs1'))
  }

  //
  // Lemmas
  //

  lemma {:verify false} P_Fail_Sound ... {}
  lemma {:verify false} P_Succ_Sound ... {}
  lemma {:verify false} Pes_Fail_Sound ... {}
  lemma {:verify false} Pes_Succ_Sound ... {}

  lemma {:verify false} Pes_Succ_Inj ... {} // TODO
  lemma {:verify false} SeqVToVS_Append ... {}

  lemma {:verify false} InductVar ... {
    assume false; // TODO
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

  lemma {:verify false} InductLiteral ... { reveal InterpExpr(); reveal InterpLiteral(); }

  lemma {:verify false} InductAbs ... {
    reveal InterpExpr();
    reveal EqValue_Closure();

/*
    var MState(env, acc, ctx, ctx') := st;
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

    assert EqValue_Closure(cv, cv');*/
  }

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

  lemma {:verify false} InductApplyEagerUnaryOp_Succ ... { reveal InterpExpr(); reveal InterpUnaryOp(); }

  lemma {:verify false} InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    InterpBinaryOp_Eq(e, e, op, v0.v, v1.v, v0.v', v1.v');
  }

  lemma {:verify false} {:fuel SeqVToVS, 2} InductApplyEagerTernaryOp_Succ ... {
    reveal InterpExpr();
    // TODO(SMH): ``SeqVToVS`` is called on literals: we shouldn't need fuel 2
    assert SeqVToVS([v0, v1, v2]) == MSeqValue([v0.v, v1.v, v2.v], [v0.v', v1.v', v2.v']);
    InterpTernaryOp_Eq(e, e, op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');
  }

  lemma {:verify false} InductApplyEagerBuiltinDisplay ... {
    reveal InterpExpr();
    Interp_Apply_Display_EqValue(e, e, ty.kind, argvs.vs, argvs.vs');
  }

  lemma {:verify false} InductApplyEagerFunctionCall ... {
    reveal InterpExpr();
    InterpFunctionCall_EqState(e, e, st.env, fv.v, fv.v', argvs.vs, argvs.vs');
  }

  lemma {:verify false} InductIf_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductIf_Succ ... { reveal InterpExpr(); }

  lemma {:verify false} InductUpdate_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductUpdate_Succ ... { reveal InterpExpr(); }

  lemma {:verify false} InductVarDecl_None_Succ ... { reveal InterpExpr(); }
  lemma {:verify false} InductVarDecl_Some_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductVarDecl_Some_Succ  ... { reveal InterpExpr(); }

  lemma {:verify false} InductBind_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductBind_Succ ... { reveal InterpExpr(); }

  lemma {:verify false} InductBlock_Fail ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx');
  }

  lemma {:verify false} InductBlock_Succ ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx');
  }
}

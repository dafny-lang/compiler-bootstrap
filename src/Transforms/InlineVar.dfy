//include "../Interop/CSharpDafnyASTModel.dfy"
//include "../Interop/CSharpInterop.dfy"
//include "../Interop/CSharpDafnyInterop.dfy"
//include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Semantics/ExprInduction.dfy"
include "../Semantics/InterpStateIneq.dfy"
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

      case Apply(Lazy(op), args) =>
        var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
        Expr.Exprs_Size_Mem(e.args, e0); // For termination
        Expr.Exprs_Size_Mem(e.args, e1); // For termination
        var (acc1, e0') :- InlineInExpr(p, acc, e0);
        var (acc2, e1') :- InlineInExpr(p, acc1, e1);
        // The second expression is not necessarily evaluated, so we need to make sure the
        // accumulators agree.
        :- Need(acc2 == acc1, ());
        Success((acc1, e.(args := [e0', e1'])))

      case Apply(Eager(op), args) =>
        var (acc', args') :- InlineInExprs(p, acc, args);
        Success((acc', e.(args := args')))

      case Block(stmts) =>
        var (_, stmts') :- InlineInExprs(p, acc, stmts);
        // We use the original acc because there is a scope
        Success((acc, e.(stmts := stmts')))

      case VarDecl(vdecls, ovals) =>
        if ovals.Some? then
          var (acc1, vals') :- InlineInExprs(p, acc, ovals.value);
          :- Need(CanUpdateVars(VarsToNameSet(vdecls), acc1.frozen), ());
          // For now, we try to inline only if there is exactly one variable
          if |vdecls| == 1 && CanInlineVar(p, vdecls[0], vals'[0]) then
            var acc2 := AddToAcc(acc, vdecls[0], vals'[0]);
            Success((acc2, EmptyBlock))
          else Success((acc1, Expr.VarDecl(vdecls, Exprs.Some(vals'))))
        else
          :- Need(CanUpdateVars(VarsToNameSet(vdecls), acc.frozen), ());
          Success((acc, e))

      case Update(vars, vals) =>
        var (acc', vals') :- InlineInExprs(p, acc, vals);
        :- Need(CanUpdateVars(SeqToSet(vars), acc'.frozen), ());
        Success((acc', e.(vals := vals')))

      case Bind(bvars, bvals, bbody) =>
        var (acc1, bvals') :- InlineInExprs(p, acc, bvals);
        :- Need(CanUpdateVars(VarsToNameSet(bvars), acc1.frozen), ()); // Not necessary, but let's make things simple for now
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
    ensures // TODO: rewrite with implication
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
  import Semantics.InterpStateIneq

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
//    && ctx'.rollback.Keys <= ctx.rollback.Keys
//    && ctx.rollback.Keys <= ctx'.rollback.Keys + acc.subst.Keys
//    && EqCtx(map x | x in ctx'.rollback.Keys :: ctx.rollback[x], ctx'.rollback)
    && EqCtx(ctx.rollback, ctx'.rollback)
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
  }

  lemma {:verify false} StateRel_Trans_Forall()
    ensures forall st0, st1, st2 | StateRel(st0, st1) && StateRel(st1, st2) :: StateRel(st0, st2)
  {
    reveal StateRel(); // BUG(https://github.com/dafny-lang/dafny/issues/2260)
    forall st0, st1, st2 | StateRel(st0, st1) && StateRel(st1, st2) ensures StateRel(st0, st2) {
      StateRel_Trans(st0, st1, st2);
    }
  }

  lemma {:verify false} StateRel_Refl(st: MState)
    ensures StateRel(st, st)
  {
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
    var ires := InlineInExpr(p, st.acc, e);
    Inv(st) ==>
    ires.Success? ==>
    var (acc1, e') := ires.value;
    var res' := InterpExpr(e', st.env, st.ctx');
    match (res, res') {
      case (Success(Return(v1, ctx1)), Success(Return(v1', ctx1'))) =>
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
    var ires := InlineInExpr(p, st.acc, e);
    && Inv(st)
    && ires.Success?
    && (
      var (acc1, e') := ires.value;
      var res' := InterpExpr(e', st.env, st.ctx');
      match (res, res') {
        case (Success(Return(v1, ctx1)), Success(Return(v1', ctx1'))) =>
          var st1 := MState(st.env, acc1, ctx1, ctx1');
          && EqValue(v1, v1')
          && Inv(st1)
          && StateRel(st, st1)
          // Additional
          && st1 == st'
          && v == MValue(v1, v1')
        case _ => false
      })
  }

  predicate {:verify false} P_Fail(st: S, e: Expr)
  {
    Inv(st) ==> InlineInExpr(p, st.acc, e).Success? ==> InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate {:verify false} Pes(st: S, es: seq<Expr>)
  {
    var res := InterpExprs(es, st.env, st.ctx);
    var ires := InlineInExprs(p, st.acc, es);
    Inv(st) ==>
    ires.Success? ==>
    var (acc1, es') := ires.value;
    var res' := InterpExprs(es', st.env, st.ctx');
    match (res, res') {
      case (Success(Return(vs1, ctx1)), Success(Return(vs1', ctx1'))) =>
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
    var ires := InlineInExprs(p, st.acc, es);
    && Inv(st)
    && ires.Success?
    && (
      var (acc1, es') := ires.value;
      var res' := InterpExprs(es', st.env, st.ctx');
      match (res, res') {
        case (Success(Return(vs1, ctx1)), Success(Return(vs1', ctx1'))) =>
          var st1 := MState(st.env, acc1, ctx1, ctx1');
          && EqSeqValue(vs1, vs1')
          && Inv(st1)
          && StateRel(st, st1)
          // Additional
          && st1 == st'
          && vs == MSeqValue(vs1, vs1')
        case _ => false
      })
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
//          assert ctx1'.rollback.Keys == ctx1.rollback.Keys; // Ok
//          assert ctx1.rollback.Keys == ctx1'.rollback.Keys + acc.subst.Keys; // Ok
  //        assert EqCtx(map x | x in ctx1'.rollback.Keys :: ctx1.rollback[x], ctx1'.rollback) by { reveal GEqCtx(); } // Ok
          assert EqCtx(ctx1.rollback, ctx1'.rollback) by { reveal GEqCtx(); } // Ok

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

  predicate UpdateState_Pre(st: S, vars: seq<string>)
  {
    && Inv(st)
    && CanUpdateVars(SeqToSet(vars), st.acc.frozen)
  }
  
  function {:verify false} UpdateState ...
    // Adding this postcondition makes the InductUpdate proofs easier
    ensures UpdateState_Pre(st, vars) ==> Inv(st') && StateRel(st, st')
  {
    var acc := st.acc;
    var ctx := st.ctx;
    var ctx' := st.ctx';
    var ctx1 := st.ctx.(locals := AugmentContext(st.ctx.locals, vars, vals.vs));
    var ctx1' := st.ctx'.(locals := AugmentContext(st.ctx'.locals, vars, vals.vs'));
    var st' := MState(st.env, st.acc, ctx1, ctx1'); // TODO: st.acc

    var b := UpdateState_Pre(st, vars);
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
//          assert ctx1'.rollback.Keys <= ctx1.rollback.Keys by { reveal EqStateWithAcc(); } // Ok
//          assert ctx1.rollback.Keys <= ctx1'.rollback.Keys + acc.subst.Keys by { reveal EqStateWithAcc(); } // Ok
//          assert EqCtx(map x | x in ctx1'.rollback.Keys :: ctx1.rollback[x], ctx1'.rollback) by { reveal EqStateWithAcc(); } // Ok
          assert EqCtx(ctx1.rollback, ctx1'.rollback) by { reveal EqStateWithAcc(); } // Ok

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

/*  function {:verify false} StateSaveToRollback_Inline(st: S, vars: seq<string>): (st':S)
  {
    // TODO
    st
  }

  function {:verify false} StateSaveToRollback_NoInline(st: S, vdecls: seq<Exprs.Var>, rhs': seq<Expr>): (st':S)
    requires |rhs'| == |vdecls|
    requires !(|vdecls| == 1 && CanInlineVar(p, vdecls[0], rhs'[0]))
    requires Inv(st)
    requires CanUpdateVars(SeqToSet(VarsToNames(vdecls)), st.acc.frozen)
    ensures Inv(st')
    ensures StateRel(st, st')
  {
    var MState(env, acc, ctx, ctx') := st;
    var vars := VarsToNames(vdecls);
    var ctx1 := SaveToRollback(st.ctx, vars);
    var ctx1' := SaveToRollback(st.ctx', vars);
    var st' := MState(st.env, acc, ctx1, ctx1');

//    assert StateRel(st, st') by {
//      if b {
//        assume false;
//      }
//    }

    st'
   }*/

  predicate {:verify false} StateSaveToRollback_Pre(st: S, vars: seq<string>)
  {
    && Inv(st)
    && CanUpdateVars(SeqToSet(vars), st.acc.frozen)
  }

  // TODO: remove this auxiliary definition
  function StateSaveToRollback_Aux(st: S, vars: seq<string>): (st':S)
    // ``StateSaveToRollback``, without pre and postconditions
  {
    var MState(env, acc, ctx, ctx') := st;
    var ctx1 := SaveToRollback(st.ctx, vars);
    var ctx1' := SaveToRollback(st.ctx', vars);
    var st' := MState(st.env, acc, ctx1, ctx1');
    st'
  }

  lemma {:verify false} StateSaveToRollback_Equiv(st: S, varseq: seq<string>)
//    requires Inv(st)
//    requires CanUpdateVars(SeqToSet(varseq), st.acc.frozen)
    requires StateSaveToRollback_Pre(st, varseq)
    ensures
      var st' := StateSaveToRollback_Aux(st, varseq);
      && Inv(st')
      && StateRel(st, st')
  {
    var st' := StateSaveToRollback_Aux(st, varseq);
    var MState(env, acc, ctx, ctx') := st;

    var vars := set x | x in varseq;
    assert vars == SeqToSet(varseq) by { reveal SeqToSet(); }
    var save := map x | x in (vars * ctx.locals.Keys) - ctx.rollback.Keys :: ctx.locals[x];
    var save' := map x | x in (vars * ctx'.locals.Keys) - ctx'.rollback.Keys :: ctx'.locals[x];

    var ctx1 := ctx.(locals := ctx.locals - vars, rollback := ctx.rollback + save);
    var ctx1' := ctx'.(locals := ctx'.locals - vars, rollback := ctx'.rollback + save');

    assert ctx1 == st'.ctx by { reveal SaveToRollback(); }
    assert ctx1' == st'.ctx' by { reveal SaveToRollback(); }

    assert EqStateWithAcc(env, acc, ctx1, ctx1') by {
      assert EqStateWithAcc_Locals(env, acc, ctx1, ctx1') by {
        assert ctx1'.locals.Keys !! acc.subst.Keys by { reveal EqStateWithAcc(); }
        assert ctx1'.locals.Keys + acc.subst.Keys == ctx1.locals.Keys by {
          assert acc.subst.Keys !! vars by {
            assert acc.subst.Keys <= acc.frozen by { reveal EqStateWithAcc(); reveal EqStateOnAcc(); }
            reveal SeqToSet();
          }
          reveal EqStateWithAcc();
        }
        assert EqCtx(map x | x in ctx1'.locals.Keys :: ctx1.locals[x], ctx1'.locals) by { reveal EqStateWithAcc(); reveal GEqCtx(); }
        assert EqStateOnAcc(env, acc, ctx1, ctx1') by {
          // TODO: Same theorem as for StateStartScope
          assume false;
        }
        reveal EqStateOnAcc();
      }
      assert EqCtx(ctx1.rollback, ctx1'.rollback) by {
        assert save.Keys == save'.Keys by {
          assert ctx'.locals.Keys + acc.subst.Keys == ctx.locals.Keys by { reveal EqStateWithAcc(); }
          assert acc.subst.Keys !! SeqToSet(varseq) by { reveal SeqToSet(); } // TODO(SMH): this proof shouldn't succeed?? (should need `reveal EqStateOnAcc`)
          assert ctx.rollback.Keys == ctx'.rollback.Keys by { reveal EqStateWithAcc(); reveal GEqCtx(); }
          reveal SeqToSet();
        }
        assert forall x | x in save.Keys * save'.Keys :: EqValue(save[x], save'[x]) by {
          assert ctx'.locals.Keys + acc.subst.Keys == ctx.locals.Keys by { reveal EqStateWithAcc(); }
          assert EqCtx(map x | x in ctx'.locals.Keys :: ctx.locals[x], ctx'.locals) by { reveal EqStateWithAcc(); }
          reveal GEqCtx();
        }
        assert EqCtx(ctx.rollback, ctx'.rollback) by { reveal EqStateWithAcc(); }
        reveal GEqCtx();
      }
      reveal EqStateWithAcc();
    }
    assert StateRel(st, st') by {
      reveal StateRel();
    }
  }

  function {:verify false} StateSaveToRollback ...
    // TODO: remove
//    ensures StateSaveToRollback_Pre(st, vars) ==> Inv(st') && StateRel(st, st')
  {
    var st' := StateSaveToRollback_Aux(st, vars);

/*    var b := StateSaveToRollback_Pre(st, vars);
    assert b ==> Inv(st') && StateRel(st, st') by {
      if b {
        StateSaveToRollback_Equiv(st, vars);
      }
    }*/

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
//          assert ctx1'.rollback.Keys <= ctx1.rollback.Keys;
//          assert ctx1.rollback.Keys <= ctx1'.rollback.Keys + acc.subst.Keys;
//          assert EqCtx(map x | x in ctx1'.rollback.Keys :: ctx1.rollback[x], ctx1'.rollback) by { reveal GEqCtx(); }
          assert EqCtx(ctx1.rollback, ctx1'.rollback) by { reveal GEqCtx(); }
          reveal EqStateWithAcc();
        }
        assert StateRel(st, st') by { reveal StateRel(); }
      }
    }
//    reveal GEqCtx();
    st'
  }

  predicate EndScope_StateSmaller(ctx: State, ctx': State)
    // Auxiliary predicate
  {
    ctx.locals.Keys <= ctx'.locals.Keys + ctx'.rollback.Keys
  }

  predicate StateEndScope_Pre(st0: S, st: S)
  {
    && Inv(st0)
    && Inv(st)
    && EndScope_StateSmaller(st0.ctx, st.ctx)
    && EndScope_StateSmaller(st0.ctx', st.ctx')
  }

  function {:verify false} StateEndScope ...
    ensures StateEndScope_Pre(st0, st) ==> Inv(st') && StateRel(st0, st')
  {
    var MState(env, acc, ctx0, ctx0') := st0;
    var ctx1 := EndScope(st0.ctx, st.ctx);
    var ctx1' := EndScope(st0.ctx', st.ctx');
    var st' := MState(env, acc, ctx1, ctx1');
    var b := StateEndScope_Pre(st0, st);
    assert b ==> Inv(st') && StateRel(st0, st') by {
      if b {
        assert EqStateWithAcc(env, acc, ctx1, ctx1') by {
          assert EqStateWithAcc_Locals(env, acc, ctx1, ctx1') by {
            assert ctx1'.locals.Keys !! acc.subst.Keys by { reveal EqStateWithAcc(); }
            assert ctx1'.locals.Keys + acc.subst.Keys == ctx1.locals.Keys by {
              assert ctx0.locals.Keys <= st.ctx.locals.Keys + st.ctx.rollback.Keys;
              assert ctx0'.locals.Keys <= st.ctx'.locals.Keys + st.ctx'.rollback.Keys;
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
//          assert ctx1'.rollback.Keys <= ctx1.rollback.Keys by { reveal EqStateWithAcc(); }
//          assert ctx1.rollback.Keys <= ctx1'.rollback.Keys + acc.subst.Keys by { reveal EqStateWithAcc(); }
//          assert EqCtx(map x | x in ctx1'.rollback.Keys :: ctx1.rollback[x], ctx1'.rollback) by { reveal EqStateWithAcc(); }
          assert EqCtx(ctx1.rollback, ctx1'.rollback) by { reveal EqStateWithAcc(); }
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
    var (_, e') := InlineInExpr(p, st.acc, e).value;
    var Return(v1', ctx1') := InterpExpr(e', st.env, st.ctx').value;
    var (acc1, _) := InlineInExpr(p, st.acc, e).value;
    (MState(st.env, acc1, ctx1, ctx1'), MValue(v1, v1'))
  }

  function {:verify false} Pes_Step ...
  {
    var Return(vs1, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    var (_, es') := InlineInExprs(p, st.acc, es).value;
    var Return(vs1', ctx1') := InterpExprs(es', st.env, st.ctx').value;
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

  lemma {:verify false} Pes_Succ_Inj ... {}
  lemma {:verify false} SeqVToVS_Append ... {}

  lemma {:verify false} InductVar ... {
    reveal InterpExpr();
    reveal GEqCtx();

    var env := st.env;
    var acc := st.acc;
    var x := e.name;

    StateRel_Refl(st);

    if x in acc.subst.Keys {
      // We inlined the variable
      var (acc', e') := InlineInExpr(p, acc, e).value;
      assert acc' == acc;
      assert e' == acc.subst[x];

      var res := InterpExpr(e, st.env, st.ctx);
      var res' := InterpExpr(e', st.env, st.ctx');

      var ctx := st.ctx;
      var ctx' := st.ctx';
      assert res' == InterpExpr(acc.subst[x], env, ctx');
      assert
        match res' {
          case Success(Return(v, ctx'')) =>
            && x in ctx.locals.Keys
            && ctx'' == ctx'
            && v == ctx.locals[x]
          case Failure(_) => false
        }
      by {
        reveal EqStateWithAcc();
        reveal EqStateOnAcc();
      }

      var Return(v, _) := res.value;
      EqValue_Refl(v);
    }
    else {
      // We didn't inline the variable
      // Start by looking in the local context
      var res0 := TryGetVariable(st.ctx.locals, x, UnboundVariable(x));
      if res0.Success? {
        assert x in st.ctx.locals && x in st.ctx'.locals && EqValue(st.ctx.locals[x], st.ctx'.locals[x]) by {
          reveal EqStateWithAcc();
          reveal GEqCtx();
        }
      }
      else {
        assert x !in st.ctx.locals && x !in st.ctx'.locals by {
          reveal EqStateWithAcc();
        }

        // Not in the local context: look in the global context
        assert x in env.globals;
        EqValue_Refl(env.globals[x]);
      }
    }
  }

  lemma {:verify false} InductLiteral ... { reveal InterpExpr(); reveal InterpLiteral(); StateRel_Refl(st); }

  lemma {:verify false} InductAbs ... {
    assume false; // TODO
    reveal InterpExpr();
    reveal EqValue_Closure();
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

    assert EqValue_Closure(cv, cv');
    StateRel_Refl(st);
  }

  lemma {:verify false} InductAbs_CallState ... {
    reveal InterpExpr();
    reveal InterpCallFunctionBody();
    reveal BuildCallState();
  }

  lemma {:verify false} InductExprs_Nil ... { reveal InterpExprs(); StateRel_Refl(st); }
  lemma {:verify false} InductExprs_Cons ... {
    reveal InterpExprs();
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductApplyLazy_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductApplyLazy_Succ ... {
    reveal InterpExpr();
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductApplyEager_Fail ... { reveal InterpExpr(); }

  lemma {:verify false} InductApplyEagerUnaryOp_Succ ... {
    reveal InterpExpr();
    reveal InterpUnaryOp();
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    var (_, e') := InlineInExpr(p, st.acc, e).value;
    InterpBinaryOp_Eq(e, e', op, v0.v, v1.v, v0.v', v1.v');
    StateRel_Trans_Forall();
  }

  lemma {:verify false} {:fuel SeqVToVS, 2} InductApplyEagerTernaryOp_Succ ... {
    reveal InterpExpr();
    var (_, e') := InlineInExpr(p, st.acc, e).value;
    // TODO(SMH): ``SeqVToVS`` is called on literals: we shouldn't need fuel 2
    assert SeqVToVS([v0, v1, v2]) == MSeqValue([v0.v, v1.v, v2.v], [v0.v', v1.v', v2.v']);
    InterpTernaryOp_Eq(e, e', op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductApplyEagerBuiltinDisplay ... {
    reveal InterpExpr();
    var (_, e') := InlineInExpr(p, st.acc, e).value;
    Interp_Apply_Display_EqValue(e, e', ty.kind, argvs.vs, argvs.vs');
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductApplyEagerFunctionCall ... {
    reveal InterpExpr();
    var (_, e') := InlineInExpr(p, st.acc, e).value;
    InterpFunctionCall_EqState(e, e', st.env, fv.v, fv.v', argvs.vs, argvs.vs');
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductIf_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductIf_Succ ... { reveal InterpExpr(); StateRel_Trans_Forall(); }

  lemma {:verify false} InductUpdate_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductUpdate_Succ ... {
    reveal InterpExpr();
    assert UpdateState_Pre(st1, vars) by {
      assert Inv(st1);
      assert CanUpdateVars(SeqToSet(vars), st1.acc.frozen) by {
        reveal SeqToSet();
        reveal VarsToNameSet();
      }
    }
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductVarDecl_None_Succ ... {
    reveal InterpExpr();

    assert CanUpdateVars(SeqToSet(vars), st.acc.frozen) by { reveal SeqToSet(); reveal VarsToNameSet(); }
    StateSaveToRollback_Equiv(st, vars);
    assert P_Succ(st, e, st1, UnitV);
  }

  lemma {:verify false} InductVarDecl_Some_Fail ... { reveal InterpExpr(); }

/*
  // Custom lemma we add for the VarDecl case where we inline variables
  lemma {:verify false} InductVarDecl_Some_Succ_Inline(
      st: S, e: Expr, vdecls: seq<Exprs.Var>, vars: seq<string>, vals: seq<Expr>, st1: S, values: VS,
      acc1: Acc, vals': seq<Expr>, acc2: Acc,
      st2: S, st3: S
      )
    requires e.VarDecl? && e.vdecls == vdecls && e.ovals.Some? && e.ovals.value == vals
    requires !P_Fail(st, e)
    requires Pes_Succ(st, vals, st1, values)
    requires vars == VarsToNames(vdecls)
    requires Success((acc1, vals')) == InlineInExprs(p, st.acc, vals)
    requires |vdecls| == 1 && CanInlineVar(p, vdecls[0], vals'[0])
    requires acc2 == AddToAcc(st.acc, vdecls[0], vals'[0])
    ensures 
    
/*    requires st2 == StateSaveToRollback(st1, vars)
    requires VS_UpdateStatePre(st2, vars, values) ==> st3 == UpdateState(st2, vars, values) // Slightly convoluted, but ``UpdateState`` has a pre
    ensures VS_UpdateStatePre(st2, vars, values)
    // This is not necessary but can help the proofs - what really matters is that ``StateSaveToRollback``
    // and ``UpdateState`` appear somewhere
    ensures P_Succ(st, e, st3, UnitV) // TODO: remove: it is not true in the case of variables inlining. Maybe: P_Succ(...) ==> P(...) (trivially true, but can help Z3)?
    ensures P(st, e)*/

  {
    assume false; // TODO
  }*/

  lemma {:verify false} InductVarDecl_Some_Succ_Inline(
      st: S, e: Expr, vdecls: seq<Exprs.Var>, vars: seq<string>, vals: seq<Expr>)
    requires e.VarDecl? && e.vdecls == vdecls && e.ovals.Some? && e.ovals.value == vals
    requires !P_Fail(st, e)
    ensures P(st, e)
  {
    var ires := InlineInExpr(p, st.acc, e);
    assert Inv(st);
    assert ires.Success?;
    var (_, e') := ires.value;

    var res := InterpExpr(e, st.env, st.ctx);
    var res' := InterpExpr(e', st.env, st.ctx');

    assert res.Success?;
    var Return(vf, ctxf) := res.value;
    
    
    assume false;
/*    
    match (res, res') {
      case (Success(Return(vf, ctxf)), Success(Return(vf', ctxf'))) =>
        var (accf, _) := InlineInExpr(p, st.acc, e).value;
        var stf := MState(st.env, accf, ctxf, ctxf');
        && EqValue(vf, vf')
        && Inv(stf)
        && StateRel(st, stf)
      case (Failure(_), _) => true
      case _ => false
    }*/

    assume false; // TODO
  }

  lemma {:verify false} InductVarDecl_Some_Succ  ... {
    reveal InterpExpr();
    var (acc1, vals') := InlineInExprs(p, st.acc, vals).value;
    if |vdecls| == 1 && CanInlineVar(p, vdecls[0], vals'[0]) {
      // Case where we add variables to inline to the accumulator
      var acc2 := AddToAcc(st.acc, vdecls[0], vals'[0]);

      assert VS_UpdateStatePre(st2, vars, values);

//      assume P_Succ(st, e, st3, UnitV); // TODO: actually, we can't prove that
      assume false; // TODO
    }
    else {
      // Case where the accumulator is unchanged
      assert CanUpdateVars(SeqToSet(vars), st1.acc.frozen) by { reveal SeqToSet(); reveal VarsToNameSet(); }
      StateSaveToRollback_Equiv(st1, vars);
      assert P_Succ(st, e, st3, UnitV) by {
        var res := InterpExpr(e, st.env, st.ctx);
        var ires := InlineInExpr(p, st.acc, e);
        assert Inv(st);
        assert ires.Success?;
        var (_, e') := ires.value;
        var res' := InterpExpr(e', st.env, st.ctx');

        var Return(v1, ctx1) := res.value;
        var Return(v1', ctx1') := res'.value;
        var (acc1, _) := InlineInExpr(p, st.acc, e).value;
        var st3' := MState(st.env, acc1, ctx1, ctx1');

        assert EqValue(v1, v1');
        assert Inv(st3');
        assert StateRel(st, st3') by {
          StateRel_Trans(st, st1, st2);
          assert StateRel(st2, st3);
          StateRel_Trans(st, st2, st3);
        }
        assert st3' == st3;
        assert UnitV == MValue(v1, v1');
      }
    }
  }

  lemma {:verify false} InductBind_Fail ... { assume false; reveal InterpExpr(); } // TODO

  lemma {:verify false} InductBind_Succ ... { assume false; reveal InterpExpr(); } // TODO

  lemma {:verify false} InductBlock_Fail ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
    var (_, e') := InlineInExpr(p, st.acc, e).value;
    var stmts' := e'.stmts;
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
    InterpExprs_Block_Equiv_Strong(stmts', st.env, st_start.ctx');
  }

  lemma {:verify false} InductBlock_Succ ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
    var (_, e') := InlineInExpr(p, st.acc, e).value;
    var stmts' := e'.stmts;
    InterpExprs_Block_Equiv_Strong(stmts, st.env, st_start.ctx);
    InterpExprs_Block_Equiv_Strong(stmts', st.env, st_start.ctx');

    assert Inv(st);
    assert Inv(st_stmts);
    assert EndScope_StateSmaller(st.ctx, st_stmts.ctx) by {
      InterpStateIneq.InterpBlock_Exprs_StateSmaller(stmts, st.env, st_start.ctx);
    }
    assert EndScope_StateSmaller(st.ctx', st_stmts.ctx') by {
      InterpStateIneq.InterpBlock_Exprs_StateSmaller(stmts', st.env, st_start.ctx');
    }
    assert StateEndScope_Pre(st, st_stmts);
  }
}

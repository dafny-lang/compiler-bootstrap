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
include "../Semantics/EqInterpRefl.dfy"
include "../Semantics/Pure.dfy"
//include "InterpStateIneq.dfy"

module Bootstrap.Transforms.InlineVar.Subst.Base {
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
    
  function method {:verify false} {:verify false} SubstInExpr(acc: SubstAcc, e: Expr): (e':Expr)
//    requires forall x | x in acc.subst.Keys :: Deep.All_Expr(acc.subst[x], NotVarDecl)
//    requires Deep.All_Expr(e, NotVarDecl)
//    ensures Deep.All_Expr(e', NotVarDecl)
    decreases e.Size(), 0
    // Substitute in an expression.
    //
    // We don't check if variable updates lead to shadowing: this should have been checked before.
  {
    reveal Interp.SupportsInterp();

    match e {
      case Var(v) =>
        if v in acc.subst.Keys then acc.subst[v] else e

      case Literal(_) => e

      case Abs(vars, body) =>
        // TODO(SMH): for now we ignore abstractions because we need to update the closures so
        // that they carry the global environment
//        var body' := SubstInExpr(acc, body);
//        e.(body := body')
        e

      case Apply(Lazy(op), args) =>
        var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
        Expr.Exprs_Size_Mem(e.args, e0); // For termination
        Expr.Exprs_Size_Mem(e.args, e1); // For termination
        var e0' := SubstInExpr(acc, e0);
        var e1' := SubstInExpr(acc, e1);
        e.(args := [e0', e1'])

      case Apply(Eager(op), args) =>
        var args' := SubstInExprs(acc, args);
        e.(args := args')

      case Block(stmts) =>
        var stmts' := SubstInExprs(acc, stmts);
        // We use the original acc because there is a scope
        e.(stmts := stmts')

      case Update(vars, vals) =>
        var vals' := SubstInExprs(acc, vals);
        e.(vals := vals')

      case Bind(bvars, bvals, bbody) =>
        var bvals' := SubstInExprs(acc, bvals);
        var bbody' := SubstInExpr(acc, bbody);
        Expr.Bind(bvars, bvals', bbody')

      case If(cond, thn, els) =>
        var cond' := SubstInExpr(acc, cond);
        var thn' := SubstInExpr(acc, thn);
        var els' := SubstInExpr(acc, els);
        Expr.If(cond', thn', els')

      case VarDecl(_, _) =>
        // We ignore the ``VarDecl`` case: in the proofs, we take as precondition that the
        // expression doesn't contain any variable declaration. We don't add it as a precondition
        // here because it is a bit cumbersome.
        e
    }
  }

  function method {:verify false} {:verify false} SubstInExprs(acc: SubstAcc, es: seq<Expr>) :
    (es': seq<Expr>)
//    requires forall x | x in acc.subst.Keys :: Deep.All_Expr(acc.subst[x], NotVarDecl)
//    requires forall e | e in es :: Deep.All_Expr(e, NotVarDecl)
//    ensures forall e | e in es' :: Deep.All_Expr(e, NotVarDecl)
    ensures |es'| == |es|
    decreases Expr.Exprs_Size(es), 1
  {
    if es == [] then []
    else
      var e' := SubstInExpr(acc, es[0]);
      var es' := SubstInExprs(acc, es[1..]);
      [e'] + es'
  }
}

module Bootstrap.Transforms.InlineVar.Subst.BaseProofs refines Semantics.ExprInduction {
  import opened Semantics.Pure
  import opened Base
  import Semantics.InterpStateIneq
  import Semantics.EqInterpRefl

  type {:verify false} Value = Interp.Value
  type {:verify false} Context = Interp.Context
//  const {:verify false} VarsToNames := Interp.VarsToNames

  const {:verify false} p: (Exprs.TypedVar, Expr) -> bool

//  const EmptyCtx: Context := map[]

  // - `ctx`: the environment to execute the original expression
  // - `ctx'`: the environment to execute the expression on which we performed inlinings
  datatype {:verify false} MState = MState(env: Environment, acc: SubstAcc, ctx: State, ctx': State)
  datatype {:verify false} MValue = MValue(v: Value, v': Value)
  datatype {:verify false} MSeqValue = MSeqValue(vs: seq<Value>, vs': seq<Value>)

  // TODO(SMH): remove `ctx`?
  predicate {:verify false} {:opaque} AccValid(env: Environment, acc: SubstAcc, ctx: State, ctx': State)
//    requires acc.subst.Keys <= ctx.locals.Keys
  {
//    && acc.subst.Keys <= acc.frozen
//    && (forall x | x in acc.subst.Keys :: VarsOfExpr(acc.subst[x]) <= acc.frozen)
    && acc.subst.Keys <= ctx'.locals.Keys
    && forall x | x in acc.subst.Keys :: Deep.All_Expr(acc.subst[x], NotVarDecl)
    && (forall x | x in acc.subst.Keys ::
       var res := InterpExpr(acc.subst[x], env, ctx');
       && res.Success?
       && res.value == Return(ctx'.locals[x], ctx'))
  }

  predicate {:verify false} {:opaque} EqStateWithAcc(env: Environment, acc: SubstAcc, ctx: State, ctx': State)
    // Predicate stating the conditions under which two states are equivalent under the presence of
    // an inlining accumulator.
  {
    && ctx.rollback == ctx'.rollback == map []
    && EqCtx(ctx.locals, ctx'.locals)
    && AccValid(env, acc, ctx, ctx')
  }

  predicate {:verify false} Inv(st: MState)
  {
    EqStateWithAcc(st.env, st.acc, st.ctx, st.ctx')
  }

/*  lemma {:verify false} VarsOfExpr_ChildrenSmaller(read: bool, e: Expr)
    ensures forall e' | e' in e.Children() :: VarsOfExpr(read, e') <= VarsOfExpr(read, e)
  {
    assume false; // TODO
  }*/

  predicate {:verify false} {:opaque} AccNoIntersect(acc: SubstAcc, vars: set<string>)
  {
    // The variables used in the substitution don't intersect the variables updated in the expression.
    // Note that we are voluntarily conservative to simplify the proofs - we can make the theorems
    // more precise in the future.
    && forall x | x in acc.subst :: ({x} + AllVarsOfExpr(acc.subst[x])) * vars == {}
  }

  predicate {:verify false} ExprValid(acc: SubstAcc, e: Expr)
  {
//    Deep.AllImpliesChildren(e, NotVarDecl);
//    VarsOfExpr_ChildrenSmaller(false, e);
    && Deep.All_Expr(e, NotVarDecl)
    // We don't need to use the Deep predicate (it is actually equivalent to not using it) but
    // that makes the proofs easier.
    && Deep.All_Expr(e, var f := (e: Syntax.Expr) => AccNoIntersect(acc, UpdtVarsOfExpr(e)); f)
//    && forall x | x in acc.subst :: ({x} + AllVarsOfExpr(acc.subst[x])) * UpdtVarsOfExpr(e) == {}
  }

/*  lemma {:verify false} ExprsValid_ImpliesTail(acc: SubstAcc, e: Expr, es: seq<Expr>)
    requires |es| > 0
    requires ExprsValid(st, [e] + es)
    requires ExprValid(st, e)
    ensures forall e' | e' in e.Children() :: ExprValid(st, e')
  {
    reveal ExprValid();
    Deep.AllImpliesChildren(e, NotVarDecl);
    VarsOfExpr_ChildrenSmaller(false, e);
  }*/


/*  predicate ExprValid(st: MState, e: Expr)
    ensures ExprValid(st, e) ==> forall e' | e' in e.Children() :: ExprValid_Aux(st, e')
  {
    var b := ExprValid_Aux(st, e);
    assert b ==> forall e' | e' in e.Children() :: ExprValid_Aux(st, e') by {
      if b {
        ExprValid_ImpliesChildren(st, e);
      }
    }
    b
  }*/

  predicate {:verify false} ExprsValid(acc: SubstAcc, es: seq<Expr>)
  {
    forall e | e in es :: ExprValid(acc, e)
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

  type {:verify false} S(!new) = MState
  type {:verify false} V(!new) = MValue
  type {:verify false} VS(!new) = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

  predicate {:verify false} P(st: S, e: Expr)
  {
    var res := InterpExpr(e, st.env, st.ctx);
    var e' := SubstInExpr(st.acc, e);
    var res' := InterpExpr(e', st.env, st.ctx');
    Inv(st) ==>
    ExprValid(st.acc, e) ==>
    match (res, res') {
      case (Success(Return(v1, ctx1)), Success(Return(v1', ctx1'))) =>
        var st1 := MState(st.env, st.acc, ctx1, ctx1');
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
    var e' := SubstInExpr(st.acc, e);
    var res' := InterpExpr(e', st.env, st.ctx');
    && Inv(st)
    && ExprValid(st.acc, e)
    && (match (res, res') {
        case (Success(Return(v1, ctx1)), Success(Return(v1', ctx1'))) =>
          var st1 := MState(st.env, st.acc, ctx1, ctx1');
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
    Inv(st) ==> ExprValid(st.acc, e) ==> InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate {:verify false} Pes(st: S, es: seq<Expr>)
  {
    var res := InterpExprs(es, st.env, st.ctx);
    var es' := SubstInExprs(st.acc, es);
    var res' := InterpExprs(es', st.env, st.ctx');
    Inv(st) ==>
    ExprsValid(st.acc, es) ==>
    match (res, res') {
      case (Success(Return(vs1, ctx1)), Success(Return(vs1', ctx1'))) =>
        var st1 := MState(st.env, st.acc, ctx1, ctx1');
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
    var es' := SubstInExprs(st.acc, es);
    var res' := InterpExprs(es', st.env, st.ctx');
    && Inv(st)
    && ExprsValid(st.acc, es)
    && (match (res, res') {
        case (Success(Return(vs1, ctx1)), Success(Return(vs1', ctx1'))) =>
          var st1 := MState(st.env, st.acc, ctx1, ctx1');
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
    Inv(st) ==> ExprsValid(st.acc, es) ==> InterpExprs(es, st.env, st.ctx).Failure?
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

  function {:verify false} BuildClosureCallState ...
  {
    var acc := st.acc;
    var ctx := st.ctx;
    var ctx' := st.ctx';
    var ctx1 := BuildCallState(st.ctx.locals, vars, argvs.vs);
    var ctx1' := BuildCallState(st.ctx'.locals, vars, argvs.vs');
    var st' := MState(env, acc, ctx1, ctx1');
    st'
  }
  
  predicate {:verify false} UpdateState_Pre(st: S, vars: seq<string>)
  {
    && Inv(st)
    && AccNoIntersect(st.acc, SeqToSet(vars))
//    && CanUpdateVars(SeqToSet(vars), st.acc.frozen)
  }

  function {:verify false} UpdateState ...
    // Adding this postcondition makes the InductUpdate proofs easier
    ensures UpdateState_Pre(st, vars) ==> Inv(st') && StateRel(st, st')
  {
    var MState(env, acc, ctx, ctx') := st;
    var ctx1 := st.ctx.(locals := AugmentContext(st.ctx.locals, vars, vals.vs));
    var ctx1' := st.ctx'.(locals := AugmentContext(st.ctx'.locals, vars, vals.vs'));
    var st' := MState(env, st.acc, ctx1, ctx1');

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
          assert ctx1.rollback == ctx1'.rollback == map [] by { reveal EqStateWithAcc(); }
          assert EqCtx(ctx1.locals, ctx1'.locals) by { reveal EqStateWithAcc(); reveal GEqCtx(); }
          assert AccValid(env, acc, ctx1, ctx1') by {
            assert acc.subst.Keys <= ctx1'.locals.Keys by { reveal EqStateWithAcc(); reveal AccValid(); }
            assert forall x | x in acc.subst.Keys :: Deep.All_Expr(acc.subst[x], NotVarDecl) by { reveal EqStateWithAcc(); reveal AccValid(); }
            // TODO: lemma:
            // - if we update variables which don't appear in some expressions, then the result of
            //   evaluating those expressions is the same
            assume (forall x | x in acc.subst.Keys ::
               var res := InterpExpr(acc.subst[x], env, ctx1');
               && res.Success?
               && res.value == Return(ctx1'.locals[x], ctx1'));
            reveal AccValid();
          }
          reveal EqStateWithAcc();
        }

        // The two states are trivially related because the accumulator is unchanged
        assert StateRel(st, st') by { reveal StateRel(); }
      }
    }
    st'
  }

  // TODO: remove this auxiliary definition
  function {:verify false} StateSaveToRollback_Aux(st: S, vars: seq<string>): (st':S)
    // ``StateSaveToRollback``, without pre and postconditions
  {
    var MState(env, acc, ctx, ctx') := st;
    var ctx1 := SaveToRollback(st.ctx, vars);
    var ctx1' := SaveToRollback(st.ctx', vars);
    var st' := MState(st.env, acc, ctx1, ctx1');
    st'
  }

  function {:verify false} StateSaveToRollback ...
    // TODO: remove
//    ensures StateSaveToRollback_Pre(st, vars) ==> Inv(st') && StateRel(st, st')
  {
    var st' := StateSaveToRollback_Aux(st, vars);
    st'
  }

  function {:verify false} StateStartScope ...
    ensures Inv(st) ==> st' == st && StateRel(st, st')
  {
    var MState(env, acc, ctx, ctx') := st;
    var ctx1 := StartScope(ctx);
    var ctx1' := StartScope(ctx');
    var st' := MState(env, acc, ctx1, ctx1');

    assert Inv(st) ==> st' == st && StateRel(st, st') by {
        reveal EqStateWithAcc();
        reveal StateRel();
    }

    st'
  }

  predicate {:verify false} EndScope_StateSmaller(ctx: State, ctx': State)
    // Auxiliary predicate
  {
    ctx.locals.Keys <= ctx'.locals.Keys + ctx'.rollback.Keys
  }

  function {:verify false} StateEndScope ...
  {
    var MState(env, acc, ctx0, ctx0') := st0;
    var ctx1 := EndScope(st0.ctx, st.ctx);
    var ctx1' := EndScope(st0.ctx', st.ctx');
    var st' := MState(env, acc, ctx1, ctx1');
    st'
  }

  predicate {:verify false} StateEndScope_Pre(st0: S, st: S, stmts: seq<Expr>)
  {
    && Inv(st0)
    && Inv(st)
    && StateRel(st0, st)
    && EndScope_StateSmaller(st0.ctx, st.ctx)
    && EndScope_StateSmaller(st0.ctx', st.ctx')
    && AccNoIntersect(st0.acc, UpdtVarsOfExprs(stmts))
    // TODO(SMH): add condition stating that `st` was only updated over `UpdtVarsOfExprs(stmts)`
    // (we need a lemma about that).
  }

  lemma {:verify false} StateEndScope_InvRel(st0: S, st: S, stmts: seq<Expr>)
    requires StateEndScope_Pre(st0, st, stmts)
    ensures var st' := StateEndScope(st0, st); Inv(st') && StateRel(st0, st')
  {
    var MState(env, acc, ctx0, ctx0') := st0;
    var ctx1 := EndScope(st0.ctx, st.ctx);
    var ctx1' := EndScope(st0.ctx', st.ctx');
    var st' := MState(env, acc, ctx1, ctx1');
    assert st' == StateEndScope(st0, st);

    assert Inv(st') by {
      assert ctx1.rollback == ctx1'.rollback == map [] by { reveal EqStateWithAcc(); }
      assert EqCtx(ctx1.locals, ctx1'.locals) by {
        reveal EqStateWithAcc();
        reveal GEqCtx();
      }
      assert AccValid(env, acc, ctx1, ctx1') by {
        assert acc.subst.Keys <= ctx1'.locals.Keys by { reveal EqStateWithAcc(); reveal AccValid(); }
        assert forall x | x in acc.subst.Keys :: Deep.All_Expr(acc.subst[x], NotVarDecl) by { reveal EqStateWithAcc(); reveal AccValid(); }
        // TODO(SMH): lemmas: we need to talk about the expression:
        // - x !in e ==> the value for x is unchanged
        // - if we change values in the ctx, but those values don't appear in an expression,
        //   evaluating this expression leads to the same result
        assume (
           forall x | x in acc.subst.Keys ::
           var res := InterpExpr(acc.subst[x], env, ctx1');
           && res.Success?
           && res.value == Return(ctx1'.locals[x], ctx1'));
        reveal AccValid();
      }
      reveal EqStateWithAcc();
    }
    assert StateRel(st0, st') by {
      reveal StateRel();
    }
  }

  function {:verify false} P_Step ...
  {
    var Return(v1, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    var e' := SubstInExpr(st.acc, e);
    var Return(v1', ctx1') := InterpExpr(e', st.env, st.ctx').value;
    (MState(st.env, st.acc, ctx1, ctx1'), MValue(v1, v1'))
  }

  function {:verify false} Pes_Step ...
  {
    var Return(vs1, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    var es' := SubstInExprs(st.acc, es);
    var Return(vs1', ctx1') := InterpExprs(es', st.env, st.ctx').value;
    (MState(st.env, st.acc, ctx1, ctx1'), MSeqValue(vs1, vs1'))
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
      var e' := SubstInExpr(acc, e);
      assert e' == acc.subst[x];

      var res := InterpExpr(e, st.env, st.ctx);
      var res' := InterpExpr(e', st.env, st.ctx');

      var ctx := st.ctx;
      var ctx' := st.ctx';
      assert res' == InterpExpr(acc.subst[x], env, ctx');

      assert x in ctx'.locals.Keys && res'.Success? && res'.value == Return(ctx'.locals[x], ctx') by {
        reveal EqStateWithAcc();
        reveal AccValid();
      }

      assert x in ctx.locals.Keys && EqValue(ctx.locals[x], ctx'.locals[x]) by {
        reveal EqStateWithAcc();
        reveal GEqCtx();
      }
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
      assert EqCtx(cv.ctx, cv'.ctx) by { reveal EqStateWithAcc(); }
      BuildCallState_EqState(cv.ctx, cv'.ctx, vars, argvs, argvs');
      var ctx1 := BuildCallState(cv.ctx, vars, argvs);
      var ctx1' := BuildCallState(cv'.ctx, vars, argvs');
      assert EqState(ctx1, ctx1');
      
      EqInterpRefl.InterpExpr_EqRefl(body, env, ctx1, ctx1');

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
  lemma {:verify false} InductExprs_Cons ... { reveal InterpExprs(); StateRel_Trans_Forall(); }

  lemma {:verify false} InductApplyLazy_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductApplyLazy_Succ ... { reveal InterpExpr(); StateRel_Trans_Forall(); }

  lemma {:verify false} InductApplyEager_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductApplyEagerUnaryOp_Succ ... {
    reveal InterpExpr();
    reveal InterpUnaryOp();
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    var e' := SubstInExpr(st.acc, e);
    InterpBinaryOp_Eq(e, e', op, v0.v, v1.v, v0.v', v1.v');
    StateRel_Trans_Forall();
  }

  lemma {:verify false} {:fuel SeqVToVS, 2} InductApplyEagerTernaryOp_Succ ... {
    reveal InterpExpr();
    var e' := SubstInExpr(st.acc, e);
    // TODO(SMH): ``SeqVToVS`` is called on literals: we shouldn't need fuel 2
    assert SeqVToVS([v0, v1, v2]) == MSeqValue([v0.v, v1.v, v2.v], [v0.v', v1.v', v2.v']);
    InterpTernaryOp_Eq(e, e', op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductApplyEagerBuiltinDisplay ... {
    reveal InterpExpr();
    var e' := SubstInExpr(st.acc, e);
    Interp_Apply_Display_EqValue(e, e', ty.kind, argvs.vs, argvs.vs');
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductApplyEagerFunctionCall ... {
    reveal InterpExpr();
    var e' := SubstInExpr(st.acc, e);
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
      assert AccNoIntersect(st1.acc, SeqToSet(vars)) by {
        reveal AccNoIntersect();
        reveal SeqToSet();
      }
    }
    StateRel_Trans_Forall();
  }

  lemma {:verify false} InductVarDecl_None_Succ ... {} // This case is ignored
  lemma {:verify false} InductVarDecl_Some_Fail ... {} // This case is ignored
  lemma {:verify false} InductVarDecl_Some_Succ  ... {} // This case is ignored

  lemma {:verify false} InductBind_Fail ... {
    reveal InterpExpr();

    assert !Pes_Fail(st, bvals);
    forall st1, vals | Pes_Succ(st, bvals, st1, vals)
      ensures
      && VS_UpdateStatePre(st1, vars, vals)
      && !P_Fail(UpdateState(st1, vars, vals), bbody)
    {
      assert VS_UpdateStatePre(st1, vars, vals);
      assert Inv(st1);
      assume AccNoIntersect(st1.acc, SeqToSet(vars));
      assert UpdateState_Pre(st1, vars);
      var st2 := UpdateState(st1, vars, vals);
      assert Inv(st2) && StateRel(st1, st2);

      assert ExprValid(st2.acc, bbody) by {
        assert ExprValid(st2.acc, e);
        assert bbody == e.Children()[|e.Children()| - 1];
      }
      assert !P_Fail(st2, bbody);
    }
  }

  lemma {:verify false} InductBind_Succ ... { assume false; reveal InterpExpr(); } // TODO

  lemma {:verify false} InductBlock_Fail ...
  {
    reveal InterpExpr();
    reveal InterpBlock();
    reveal InterpExprs();
    reveal InterpBlock_Exprs();
    reveal InterpExprs_Block();
    
    var e' := SubstInExpr(st.acc, e);
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
    
    var e' := SubstInExpr(st.acc, e);
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
    assert AccNoIntersect(st.acc, UpdtVarsOfExprs(stmts)) by {
      reveal AccNoIntersect();
      reveal SeqToSet();
    }
    assert StateEndScope_Pre(st, st_stmts, stmts);
    StateEndScope_InvRel(st, st_stmts, stmts);
  }
}

include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Semantics/ExprInduction.dfy"
include "../Semantics/InterpStateIneq.dfy"
include "../Semantics/EqInterpRefl.dfy"
include "../Semantics/Pure.dfy"
include "VarsOfExpr.dfy"

module Bootstrap.Transforms.SubstVar.Subst.Base {
  import opened AST.Syntax
  import opened Utils.Lib
  import opened Utils.Lib.Datatypes
  import opened AST.Predicates
  import Semantics.Interp
  import opened Semantics.Equiv
  import opened Semantics.Pure
  import opened Generic
  import Shallow
  import opened VarsOfExpr

  type Environment = Interp.Environment
  type State = Interp.State
  type Expr = Interp.Expr

    
  function method SubstInExpr(acc: SubstAcc, e: Expr): (e':Expr)
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
        // TODO(SMH): for now we ignore abstractions because we need to update the closures
        // definition so that they carry the global environment (not only the local env)
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

  function method {:verify false} SubstInExprs(acc: SubstAcc, es: seq<Expr>) :
    (es': seq<Expr>)
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

module Bootstrap.Transforms.SubstVar.Subst.BaseProofs refines Semantics.ExprInduction {
  import opened Semantics.Pure
  import opened Base
  import opened VarsOfExpr
  import Semantics.InterpStateIneq
  import Semantics.EqInterpRefl

  type Value = Interp.Value
  type Context = Interp.Context

  const p: (Exprs.TypedVar, Expr) -> bool

  // - `ctx`: the environment to execute the original expression
  // - `ctx'`: the environment to execute the expression on which we performed inlinings
  datatype MState = MState(env: Environment, acc: SubstAcc, ctx: State, ctx': State)
  datatype MValue = MValue(v: Value, v': Value)
  datatype MSeqValue = MSeqValue(vs: seq<Value>, vs': seq<Value>)

  // TODO(SMH): remove `ctx`?
  predicate {:opaque} AccValid(env: Environment, acc: SubstAcc, ctx: State, ctx': State)
  {
    && acc.subst.Keys <= ctx'.locals.Keys
    && forall x | x in acc.subst.Keys :: Deep.All_Expr(acc.subst[x], NotVarDecl)
    && (forall x | x in acc.subst.Keys ::
       var res := InterpExpr(acc.subst[x], env, ctx');
       && res.Success?
       && res.value == Return(ctx'.locals[x], ctx'))
  }

  predicate {:opaque} EqStateWithAcc(env: Environment, acc: SubstAcc, ctx: State, ctx': State)
    // Predicate stating the conditions under which two states are equivalent under the presence of
    // an inlining accumulator.
  {
    && ctx.rollback == ctx'.rollback == map []
    && EqCtx(ctx.locals, ctx'.locals)
    && AccValid(env, acc, ctx, ctx')
  }

  predicate Inv(st: MState)
  {
    EqStateWithAcc(st.env, st.acc, st.ctx, st.ctx')
  }

  predicate {:opaque} AccNoIntersect(acc: SubstAcc, vars: set<string>)
  {
    // The variables used in the substitution don't intersect the variables updated in the expression.
    // Note that we are voluntarily conservative to simplify the proofs - we can make the theorems
    // more precise in the future.
    && forall x | x in acc.subst :: ({x} + AllVarsOfExpr(acc.subst[x])) * vars == {}
  }

  predicate ExprValid(acc: SubstAcc, e: Expr)
  {
    && Deep.All_Expr(e, NotVarDecl)
    // We don't need to use the Deep predicate (it is actually equivalent to not using it) but
    // that makes the proofs easier.
    && Deep.All_Expr(e, var f := (e: Syntax.Expr) => AccNoIntersect(acc, UpdtVarsOfExpr(e)); f)
  }

  predicate ExprsValid(acc: SubstAcc, es: seq<Expr>)
  {
    forall e | e in es :: ExprValid(acc, e)
  }


  predicate {:opaque} StateRel(st: MState, st': MState)
  {
    && st.acc.subst.Keys <= st'.acc.subst.Keys
    && forall x | x in st.acc.subst.Keys :: st'.acc.subst[x] == st.acc.subst[x]
  }

  lemma StateRel_Trans(st0: MState, st1: MState, st2: MState)
    requires StateRel(st0, st1)
    requires StateRel(st1, st2)
    ensures StateRel(st0, st2)
  {
    reveal StateRel();
  }

  lemma StateRel_Trans_Forall()
    ensures forall st0, st1, st2 | StateRel(st0, st1) && StateRel(st1, st2) :: StateRel(st0, st2)
  {
    reveal StateRel(); // BUG(https://github.com/dafny-lang/dafny/issues/2260)
    forall st0, st1, st2 | StateRel(st0, st1) && StateRel(st1, st2) ensures StateRel(st0, st2) {
      StateRel_Trans(st0, st1, st2);
    }
  }

  lemma StateRel_Refl(st: MState)
    ensures StateRel(st, st)
  {
    reveal StateRel();
  }

  type S(!new) = MState
  type V(!new) = MValue
  type VS(!new) = vs:MSeqValue | |vs.vs| == |vs.vs'| witness MSeqValue([], [])

  predicate P(st: S, e: Expr)
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
  
  predicate P_Succ(st: S, e: Expr, st': S, v: V)
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

  predicate P_Fail(st: S, e: Expr)
  {
    Inv(st) ==> ExprValid(st.acc, e) ==> InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate Pes(st: S, es: seq<Expr>)
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

  predicate Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
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

  predicate Pes_Fail(st: S, es: seq<Expr>)
  {
    Inv(st) ==> ExprsValid(st.acc, es) ==> InterpExprs(es, st.env, st.ctx).Failure?
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

  function BuildClosureCallState ...
  {
    var acc := st.acc;
    var ctx := st.ctx;
    var ctx' := st.ctx';
    var ctx1 := BuildCallState(st.ctx.locals, vars, argvs.vs);
    var ctx1' := BuildCallState(st.ctx'.locals, vars, argvs.vs');
    var st' := MState(env, acc, ctx1, ctx1');
    st'
  }
  
  predicate UpdateState_Pre(st: S, vars: seq<string>)
  {
    && Inv(st)
    && AccNoIntersect(st.acc, SeqToSet(vars))
  }

  function UpdateState ...
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

  function StateSaveToRollback ...
  {
    var MState(env, acc, ctx, ctx') := st;
    var ctx1 := SaveToRollback(st.ctx, vars);
    var ctx1' := SaveToRollback(st.ctx', vars);
    var st' := MState(st.env, acc, ctx1, ctx1');
    st'
  }

  function StateBindEndScope ...
  {
    var MState(env0, acc0, ctx0, ctx0') := st0;
    var MState(env, acc, ctx, ctx') := st;
    var ctx1 := ctx.(locals := CtxBindEndScope(ctx0.locals, ctx.locals, vars));
    var ctx1' := ctx'.(locals := CtxBindEndScope(ctx0'.locals, ctx'.locals, vars));
    var st' := MState(env0, acc0, ctx1, ctx1');
    st'
  }

  predicate StateBindEndScope_InvRel_Pre(
    st0: S, st0': S, st: S, vars: seq<string>, vals: VS, bbody: Expr, v: V)
  {
    && Inv(st0)
    && Inv(st)
    && StateRel(st0, st) // TODO: remove
    && VS_UpdateStatePre(st0, vars, vals)
    && st0' == UpdateState(st0, vars, vals)
    && EqSeqValue(vals.vs, vals.vs')
    && P_Succ(st0', bbody, st, v)
    && AccNoIntersect(st0.acc, UpdtVarsOfExpr(bbody))
  }

  lemma StateBindEndScope_InvRel(
    st0: S, st0': S, st: S, vars: seq<string>, vals: VS, bbody: Expr, v: V)
    requires StateBindEndScope_InvRel_Pre(st0, st0', st, vars, vals, bbody, v)
    ensures
      var st' := StateBindEndScope(st0, st, vars);
      && Inv(st')
      && StateRel(st, st')
  {
    var st' := StateBindEndScope(st0, st, vars);
    var MState(env0, acc0, ctx0, ctx0') := st;
    var MState(env1, acc1, ctx1, ctx1') := st';

    var bbody' := SubstInExpr(st0'.acc, bbody);

    assert EqStateWithAcc(env1, acc1, ctx1, ctx1') by {
      assert ctx1.rollback == ctx1'.rollback == map [] by { reveal EqStateWithAcc(); }
      assert EqCtx(ctx1.locals, ctx1'.locals) by {
        reveal EqStateWithAcc();
        reveal GEqCtx();
      }
      assert AccValid(env1, acc1, ctx1, ctx1') by {
        assert acc1.subst.Keys <= ctx1'.locals.Keys by { reveal EqStateWithAcc(); reveal AccValid(); }
        assert forall x | x in acc1.subst.Keys :: Deep.All_Expr(acc1.subst[x], NotVarDecl) by { reveal EqStateWithAcc(); reveal AccValid(); }

        // TODO(SMH): the following two assertions are not used yet - TODO: remove?
        assert st0.ctx.locals.Keys <= st.ctx.locals.Keys by {
          InterpStateIneq.InterpExpr_StateSmaller(bbody, st0'.env, st0'.ctx);
        }
        assert st0.ctx'.locals.Keys <= st.ctx'.locals.Keys by {
          InterpStateIneq.InterpExpr_StateSmaller(bbody', st0'.env, st0'.ctx');
        }

        // TODO: we need two lemmas:
        // - updating variables which don't appear in an expression leaves the evaluation unchanged
        // - if an expression doesn't syntactically updates some variables (in the sense of
        //   ``UpdtVarsOfExpr``), it also doesn't semantically update them
        assume (forall x | x in acc1.subst.Keys ::
           var res := InterpExpr(acc1.subst[x], env1, ctx1');
           && res.Success?
           && res.value == Return(ctx1'.locals[x], ctx1'));
        reveal AccValid();
      }
      reveal EqStateWithAcc();
    }
    assert StateRel(st, st') by {
      assert st.acc.subst.Keys <= st'.acc.subst.Keys;
      assert forall x | x in st.acc.subst.Keys :: st'.acc.subst[x] == st.acc.subst[x];
      reveal StateRel();
    }
  }

  function StateStartScope ...
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

  predicate EndScope_StateSmaller(ctx: State, ctx': State)
    // Auxiliary predicate
  {
    ctx.locals.Keys <= ctx'.locals.Keys + ctx'.rollback.Keys
  }

  function StateEndScope ...
  {
    var MState(env, acc, ctx0, ctx0') := st0;
    var ctx1 := EndScope(st0.ctx, st.ctx);
    var ctx1' := EndScope(st0.ctx', st.ctx');
    var st' := MState(env, acc, ctx1, ctx1');
    st'
  }

  predicate StateEndScope_Pre(st0: S, st: S, stmts: seq<Expr>)
  {
    && Inv(st0)
    && Inv(st)
    && StateRel(st0, st)
    && EndScope_StateSmaller(st0.ctx, st.ctx)
    && EndScope_StateSmaller(st0.ctx', st.ctx')
    && AccNoIntersect(st0.acc, UpdtVarsOfExprs(stmts))
    // TODO(SMH): add condition stating that `st` was only updated over `UpdtVarsOfExprs(stmts)`
    // (we need a lemma about that).
    // TODO(SMH): actually, better to follow the style of ``StateBindEndScope_InvRel_Pre``
    // (add more input parameters and put more precise information in the pre)
  }

  lemma StateEndScope_InvRel(st0: S, st: S, stmts: seq<Expr>)
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

  function P_Step ...
  {
    var Return(v1, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    var e' := SubstInExpr(st.acc, e);
    var Return(v1', ctx1') := InterpExpr(e', st.env, st.ctx').value;
    (MState(st.env, st.acc, ctx1, ctx1'), MValue(v1, v1'))
  }

  function Pes_Step ...
  {
    var Return(vs1, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    var es' := SubstInExprs(st.acc, es);
    var Return(vs1', ctx1') := InterpExprs(es', st.env, st.ctx').value;
    (MState(st.env, st.acc, ctx1, ctx1'), MSeqValue(vs1, vs1'))
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

  lemma InductLiteral ... { reveal InterpExpr(); reveal InterpLiteral(); StateRel_Refl(st); }

  lemma InductAbs ... {
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

  lemma InductAbs_CallState ... {
    reveal InterpExpr();
    reveal InterpCallFunctionBody();
    reveal BuildCallState();
  }

  lemma InductExprs_Nil ... { reveal InterpExprs(); StateRel_Refl(st); }
  lemma InductExprs_Cons ... { reveal InterpExprs(); StateRel_Trans_Forall(); }

  lemma InductApplyLazy_Fail ... { reveal InterpExpr(); }
  lemma InductApplyLazy_Succ ... { reveal InterpExpr(); StateRel_Trans_Forall(); }

  lemma InductApplyEager_Fail ... { reveal InterpExpr(); }
  lemma InductApplyEagerUnaryOp_Succ ... {
    reveal InterpExpr();
    reveal InterpUnaryOp();
    StateRel_Trans_Forall();
  }

  lemma InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    var e' := SubstInExpr(st.acc, e);
    InterpBinaryOp_Eq(e, e', op, v0.v, v1.v, v0.v', v1.v');
    StateRel_Trans_Forall();
  }

  lemma {:fuel SeqVToVS, 2} InductApplyEagerTernaryOp_Succ ... {
    reveal InterpExpr();
    var e' := SubstInExpr(st.acc, e);
    // TODO(SMH): ``SeqVToVS`` is called on literals: we shouldn't need fuel 2
    assert SeqVToVS([v0, v1, v2]) == MSeqValue([v0.v, v1.v, v2.v], [v0.v', v1.v', v2.v']);
    InterpTernaryOp_Eq(e, e', op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');
    StateRel_Trans_Forall();
  }

  lemma InductApplyEagerBuiltinDisplay ... {
    reveal InterpExpr();
    var e' := SubstInExpr(st.acc, e);
    Interp_Apply_Display_EqValue(e, e', ty.kind, argvs.vs, argvs.vs');
    StateRel_Trans_Forall();
  }

  lemma InductApplyEagerFunctionCall ... {
    reveal InterpExpr();
    var e' := SubstInExpr(st.acc, e);
    InterpFunctionCall_EqState(e, e', st.env, fv.v, fv.v', argvs.vs, argvs.vs');
    StateRel_Trans_Forall();
  }

  lemma InductIf_Fail ... { reveal InterpExpr(); }
  lemma InductIf_Succ ... { reveal InterpExpr(); StateRel_Trans_Forall(); }

  lemma InductUpdate_Fail ... { reveal InterpExpr(); }
  lemma InductUpdate_Succ ... {
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

  lemma InductVarDecl_None_Succ ... {} // This case is ignored
  lemma InductVarDecl_Some_Fail ... {} // This case is ignored
  lemma InductVarDecl_Some_Succ  ... {} // This case is ignored

  lemma InductBind_UpdateState_Pre(
    st: S, e: Expr, bvars: seq<Exprs.TypedVar>, bvals: seq<Expr>, bbody: Expr, vars: seq<string>,
    st1: S, vals: VS)
    requires e.Bind? && e.bvars == bvars && e.bvals == bvals && e.bbody == bbody
    requires !P_Fail(st, e)
    requires vars == VarsToNames(bvars)
    requires Pes_Succ(st, bvals, st1, vals)
    requires VS_UpdateStatePre(st1, vars, vals)
    ensures UpdateState_Pre(st1, vars)
    // We need this intermediary lemma to deal with context explosion
  {
    assert st1.acc == st.acc;
    assert AccNoIntersect(st.acc, UpdtVarsOfExpr(e));
    reveal AccNoIntersect();
    reveal SeqToSet();
    reveal VarsToNameSet();
  }

  lemma InductBind_Fail ... {
    reveal InterpExpr();

    assert !Pes_Fail(st, bvals);
    forall st1, vals | Pes_Succ(st, bvals, st1, vals)
      ensures
      && VS_UpdateStatePre(st1, vars, vals)
      && !P_Fail(UpdateState(st1, vars, vals), bbody)
    {
      assert UpdateState_Pre(st1, vars) by {
        InductBind_UpdateState_Pre(st, e, bvars, bvals, bbody, vars, st1, vals);
      }
      var st2 := UpdateState(st1, vars, vals);
      assert Inv(st2) && StateRel(st1, st2);

      assert ExprValid(st2.acc, bbody) by {
        assert ExprValid(st2.acc, e);
        assert bbody == e.Children()[|e.Children()| - 1];
      }
      assert !P_Fail(st2, bbody);
    }
  }

  // TODO(SMH): move up?
  predicate StateSameEnvAcc(st0: S, st1: S)
  {
    && st0.env == st1.env
    && st0.acc == st1.acc
  }

  lemma InductBind_Succ_Aux(
    st: S, e: Expr, bvars: seq<Exprs.TypedVar>, bvals: seq<Expr>, bbody: Expr, vars: seq<string>,
    st1: S, vals: VS, st2: S, st3: S, v: V, st4: S)
    requires e.Bind? && e.bvars == bvars && e.bvals == bvals && e.bbody == bbody
    requires HNFail: !P_Fail(st, e)
    requires vars == VarsToNames(bvars)
    requires HVals: Pes_Succ(st, bvals, st1, vals)
    requires VS_UpdateStatePre(st1, vars, vals)
    requires HUpdt: st2 == UpdateState(st1, vars, vals)
    requires HBody: P_Succ(st2, bbody, st3, v)
    requires HEnd: st4 == StateBindEndScope(st1, st3, vars)
    ensures P_Succ(st, e, st4, v)
    // Rem.(SMH): this lemma is exactly ``InductBind_Succ``, but with labels added to the
    // preconditions so as to control the context. Doing this is painful, but if we don't,
    // many trivial proof obligations fail because the context explodes (it seems).
  {
    assert StateSameEnvAcc(st, st1) by { reveal HVals; }
    assert StateSameEnvAcc(st1, st2) by { reveal HUpdt; }
    assert StateSameEnvAcc(st2, st3) by { reveal HBody; }
    assert StateSameEnvAcc(st3, st4) by { reveal HEnd; }

    assert AUpdt: Inv(st2) && StateRel(st1, st2) by {
      assert UpdateState_Pre(st1, vars) by {
        reveal HNFail;
        reveal HVals;
        InductBind_UpdateState_Pre(st, e, bvars, bvals, bbody, vars, st1, vals);
      }
      
      reveal HNFail;
      reveal HVals;
      reveal HUpdt;
    }

    assert AEnd: Inv(st4) && StateRel(st3, st4) by {
      reveal HNFail;
      reveal HVals;
      reveal HUpdt;
      reveal HBody;
      reveal HEnd;
      reveal AUpdt;

      assert Inv(st1);
      assert Inv(st3);
      assert StateRel(st1, st3) by {
        StateRel_Trans(st1, st2, st3);
      }
      assert EqSeqValue(vals.vs, vals.vs');
      assert AccNoIntersect(st1.acc, UpdtVarsOfExpr(bbody)) by {
        reveal AccNoIntersect();
        reveal SeqToSet();
      }
      assert StateBindEndScope_InvRel_Pre(st1, st2, st3, vars, vals, bbody, v);
      StateBindEndScope_InvRel(st1, st2, st3, vars, vals, bbody, v);
    }

    assert P_Succ(st, e, st4, v) by {
      var res := InterpExpr(e, st.env, st.ctx);
      var e': Expr := SubstInExpr(st.acc, e); // TODO(SMH): for some reason, type inference fails here
      var res' := InterpExpr(e', st.env, st.ctx');

      assert Inv(st) && ExprValid(st.acc, e) && res.Success? by { reveal HNFail; }

      var env := st.env;
      var Bind(bvars', bvals', bbody') := e'; // TODO(SMH): If we don't annotate e' with a type, this fails
      var vars := VarsToNames(bvars');
      assert bvars' == bvars;
      assert bvals' == SubstInExprs(st.acc, bvals);
      assert bbody' == SubstInExpr(st.acc, bbody);

      // The following two assertions are mostly for sanity
      assert AU: res == // unfoldind assertion
        (var Return(valsvs, ctx1) :- InterpExprs(bvals, env, st.ctx);
         var ctx2 := ctx1.(locals := AugmentContext(ctx1.locals, vars, valsvs));
         var Return(val, ctx3) :- InterpExpr(bbody, env, ctx2);
         var ctx4 := ctx3.(locals := CtxBindEndScope(ctx1.locals, ctx3.locals, vars));
         Success(Return(val, ctx4))) by {
          reveal InterpExpr();
      }

      assert AU': res' == // unfold assertion
        (var Return(valsvs', ctx1') :- InterpExprs(bvals', env, st.ctx');
         var ctx2' := ctx1'.(locals := AugmentContext(ctx1'.locals, vars, valsvs'));
         var Return(val', ctx3') :- InterpExpr(bbody', env, ctx2');
         var ctx4' := ctx3'.(locals := CtxBindEndScope(ctx1'.locals, ctx3'.locals, vars));
         Success(Return(val', ctx4'))) by {
          reveal InterpExpr();
      }

      var res1 := InterpExprs(bvals, env, st.ctx);
      var res1' := InterpExprs(bvals', env, st.ctx');
      assert res1.Success? by { reveal InterpExpr(); reveal HNFail; }
      assert res1'.Success? by { reveal HVals; }
      var Return(valsvs, ctx1) := res1.value;
      var Return(valsvs', ctx1') := res1'.value;

      assert ctx1 == st1.ctx by { reveal HVals; }
      assert ctx1' == st1.ctx' by { reveal HVals; }
      assert vals == MSeqValue(valsvs, valsvs') by { reveal HVals; }

      var ctx2 := ctx1.(locals := AugmentContext(ctx1.locals, vars, valsvs));
      var ctx2' := ctx1'.(locals := AugmentContext(ctx1'.locals, vars, valsvs'));
      assert ctx2 == st2.ctx by { reveal HUpdt; }
      assert ctx2' == st2.ctx' by { reveal HUpdt; }

      var res3 := InterpExpr(bbody, env, ctx2);
      var res3' := InterpExpr(bbody', env, ctx2');
      assert res3.Success? by { reveal InterpExpr(); reveal HNFail; }
      assert res3'.Success? by { reveal HBody; }
      var Return(val, ctx3) := res3.value;
      var Return(val', ctx3') := res3'.value;

      assert ctx3 == st3.ctx && val == v.v by { reveal HBody; }
      assert ctx3' == st3.ctx' && val' == v.v' by { reveal HBody; }

      var ctx4 := ctx3.(locals := CtxBindEndScope(ctx1.locals, ctx3.locals, vars));
      var ctx4' := ctx3'.(locals := CtxBindEndScope(ctx1'.locals, ctx3'.locals, vars));
      assert res == Success(Return(val, ctx4)) by { reveal InterpExpr(); }
      assert res' == Success(Return(val', ctx4')) by { reveal InterpExpr(); }
      assert ctx4 == st4.ctx && val == v.v by { reveal HEnd; }
      assert ctx4' == st4.ctx' && val' == v.v' by { reveal HEnd; }
      
      var stf := MState(st.env, st.acc, ctx4, ctx4');
      assert EqValue(val, val') by { reveal HBody; }
      assert Inv(st4) by { reveal AEnd; }
      assert StateRel(st, st4) by {
        assert StateRel(st, st1) by { reveal HVals; }
        assert StateRel(st1, st2) by { reveal AUpdt; }
        StateRel_Trans(st, st1, st2);
        assert StateRel(st2, st3) by { reveal HBody; }
        StateRel_Trans(st, st2, st3);
        assert StateRel(st3, st4) by { reveal AEnd; }
        StateRel_Trans(st, st3, st4);
      }
      assert stf == st4;
      assert v == MValue(val, val');
    }
  }


  lemma InductBind_Succ ... {
    InductBind_Succ_Aux(st, e, bvars, bvals, bbody, vars, st1, vals, st2, st3, v, st4);
  }

  lemma InductBlock_Fail ...
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

  lemma InductBlock_Succ ...
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

include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "Interp.dfy"
include "Equiv.dfy"

module Bootstrap.Semantics.ExprInduction {

abstract module Ind {
  import opened AST.Syntax
  import opened Utils.Lib
  import opened AST.Predicates
  import opened Interp
  import opened Values
  import opened Equiv
  import opened Utils.Lib.Datatypes

  type {:verify false} Expr = Interp.Expr

  //
  // Declarations
  //

  type {:verify false} S(!new)
  type {:verify false} V(!new)
  type {:verify false} VS(!new)

  predicate {:verify false} P(st: S, e: Expr)
  predicate {:verify false} P_Succ(st: S, e: Expr, st': S, v: V) // Success
  predicate {:verify false} P_Fail(st: S, e: Expr) // Failure

  predicate {:verify false} Pes(st: S, es: seq<Expr>)
  predicate {:verify false} Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS) // Success
  predicate {:verify false} Pes_Fail(st: S, es: seq<Expr>) // Failure
    
  function {:verify false} AppendValue(v: V, vs: VS): VS // Returns: [v] + vs
  function {:verify false} ToSeq(vs: seq<V>): VS // TODO(SMH): rename to `ToSeqValue`

  predicate VS_CallStatePre(vars: seq<string>, argvs: VS)

  function {:verify false} BuildClosureCallState(st: S, vars: seq<string>, body: Expr, env: Environment, argvs: VS): S
    requires VS_CallStatePre(vars, argvs)

  // DISCUSS: can't get the postcondition with a constant
  function {:verify false} GetNilVS(): (vs:VS)
    ensures vs == ToSeq([])

  ghost const {:verify false} NilVS:VS := GetNilVS()

  function {:verify false} P_Step(st: S, e: Expr): (res: (S, V))
    requires P(st, e)
    requires !P_Fail(st, e)
    ensures P_Succ(st, e, res.0, res.1)

  function {:verify false} P_StepState(st: S, e: Expr): S
    requires P(st, e)
    requires !P_Fail(st, e)
  {
    P_Step(st, e).0
  }

  function {:verify false} P_StepValue(st: S, e: Expr): V
    requires P(st, e)
    requires !P_Fail(st, e)
  {
    P_Step(st, e).1
  }

  function {:verify false} Pes_Step(st: S, es: seq<Expr>): (res: (S, VS))
    requires Pes(st, es)
    requires !Pes_Fail(st, es)
    ensures Pes_Succ(st, es, res.0, res.1)

  function {:verify false} Pes_StepState(st: S, es: seq<Expr>): S
    requires Pes(st, es)
    requires !Pes_Fail(st, es)
  {
    Pes_Step(st, es).0
  }

  function {:verify false} Pes_StepValue(st: S, es: seq<Expr>): VS
    requires Pes(st, es)
    requires !Pes_Fail(st, es)
  {
    Pes_Step(st, es).1
  }

  lemma {:verify false} P_Fail_Sound(st: S, e: Expr)
    requires P_Fail(st, e)
    ensures P(st, e)

  lemma {:verify false} P_Succ_Sound(st: S, e: Expr, st': S, v: V)
    requires P_Succ(st, e, st', v)
    ensures P(st, e)

  lemma {:verify false} Pes_Fail_Sound(st: S, es: seq<Expr>)
    requires Pes_Fail(st, es)
    ensures Pes(st, es)

  lemma {:verify false} Pes_Succ_Sound(st: S, es: seq<Expr>, st': S, vs: VS)
    requires Pes_Succ(st, es, st', vs)
    ensures Pes(st, es)

  lemma {:verify false} Pes_Succ_Inj(st: S, es: seq<Expr>, st1: S, st1': S, vs: VS, vs': VS)
    requires Pes_Succ(st, es, st1, vs)
    requires Pes_Succ(st, es, st1', vs')
    ensures st1 == st1'
    ensures vs == vs'

  lemma {:verify false} ToSeq_Append(v: V, vs: seq<V>)
    ensures AppendValue(v, ToSeq(vs)) == ToSeq([v] + vs)

  lemma {:verify false} InductVar(st: S, e: Expr)
    requires e.Var?
    requires !P_Fail(st, e)
    ensures P(st, e)

  lemma {:verify false} InductLiteral(st: S, e: Expr)
    requires e.Literal?
    ensures P(st, e)

  lemma {:verify false} InductAbs(st: S, e: Expr, vars: seq<string>, body: Expr)
    requires e.Abs? && e.vars == vars && e.body == body
    requires !P_Fail(st, e)
    requires forall env, argvs | VS_CallStatePre(vars, argvs) :: P(BuildClosureCallState(st, vars, body, env, argvs), body)
    ensures P(st, e)

  lemma {:verify false} InductAbs_CallState(st: S, e: Expr, vars: seq<string>, body: Expr, env: Environment, argvs: VS, st_ret: S, retv: V)
    requires e.Abs? && e.vars == vars && e.body == body
    requires VS_CallStatePre(vars, argvs)
    requires !P_Fail(st, e)
//    requires !P_Fail(BuildClosureCallState(st, vars, body, env, argvs), body)
    requires P_Succ(BuildClosureCallState(st, vars, body, env, argvs), body, st_ret, retv)
    ensures P(BuildClosureCallState(st, vars, body, env, argvs), body)

  lemma {:verify false} InductExprs_Nil(st: S)
    ensures !Pes_Fail(st, []) ==> Pes_Succ(st, [], st, NilVS) // Pes_Fail: because, for instance, the state may not satisfy the proper invariant

  // TODO: explain how the values are combined?
  lemma {:verify false} InductExprs_Succ_Impl(st: S, e: Expr, es: seq<Expr>)
    requires Pes(st, [e] + es)
    requires !Pes_Fail(st, [e] + es)
    requires P(st, e)
    ensures !P_Fail(st, e)
    ensures Pes(P_StepState(st, e), es) ==> !Pes_Fail(P_StepState(st, e), es)
    ensures
      Pes(P_StepState(st, e), es) ==>
      var (st1, v) := P_Step(st, e);
      var (st2, vs) := Pes_Step(st1, es);
      Pes_Succ(st, [e] + es, st2, AppendValue(v, vs))

  // DISCUSS: ApplyLazy is a special case
  lemma {:verify false} InductApplyLazy(st: S, e: Expr, arg0: Expr, arg1: Expr)
    requires e.Apply? && e.aop.Lazy? && e.args == [arg0, arg1]
    requires !P_Fail(st, e)
    ensures P(st, e)

  lemma {:verify false} InductApplyEager_Fail(st: S, e: Expr, args: seq<Expr>)
    requires e.Apply? && e.aop.Eager? && e.args == args
    requires Pes_Fail(st, args)
    ensures P(st, e)

  lemma {:verify false} InductApplyEagerUnaryOp_Succ(st: S, e: Expr, op: UnaryOps.T, arg0: Expr, st1: S, v0: V)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.UnaryOp? && e.aop.eOp.uop == op && e.args == [arg0]
    requires !P_Fail(st, e)
    requires P_Succ(st, arg0, st1, v0)
    requires Pes(st, [arg0])
    requires !Pes_Fail(st, [arg0])
    requires Pes_StepValue(st, [arg0]) == ToSeq([v0])
    ensures P(st, e)

  lemma {:verify false} InductApplyEagerBinaryOp_Succ(st: S, e: Expr, op: BinaryOps.T, arg0: Expr, arg1: Expr, st1: S, v0: V, st2: S, v1: V)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.BinaryOp? && e.aop.eOp.bop == op && e.args == [arg0, arg1]
    requires !P_Fail(st, e)
    requires P_Succ(st, arg0, st1, v0)
    requires P_Succ(st1, arg1, st2, v1)
    requires Pes(st, [arg0, arg1])
    requires !Pes_Fail(st, [arg0, arg1])
    requires Pes_StepValue(st, [arg0, arg1]) == ToSeq([v0, v1])
    ensures P(st, e)

  lemma {:verify false} InductApplyEagerTernaryOp_Succ(st: S, e: Expr, op: TernaryOps.T, arg0: Expr, arg1: Expr, arg2: Expr, st1: S, v0: V, st2: S, v1: V, st3: S, v2: V)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.TernaryOp? && e.aop.eOp.top == op && e.args == [arg0, arg1, arg2]
    requires !P_Fail(st, e)
    requires P_Succ(st, arg0, st1, v0)
    requires P_Succ(st1, arg1, st2, v1)
    requires P_Succ(st2, arg2, st3, v2)
    requires Pes(st, [arg0, arg1, arg2])
    requires !Pes_Fail(st, [arg0, arg1, arg2])
    requires Pes_StepValue(st, [arg0, arg1, arg2]) == ToSeq([v0, v1, v2])
    ensures P(st, e)

  lemma {:verify false} InductApplyEagerBuiltinDisplay(st: S, e: Expr, ty: Types.Type, args: seq<Expr>, st1: S, argvs: VS)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.Builtin? && e.aop.eOp.builtin.Display? && e.aop.eOp.builtin.ty == ty && e.args == args
    requires !P_Fail(st, e)
    requires Pes_Succ(st, args, st1, argvs)
    ensures P(st, e)

  lemma {:verify false} InductApplyEagerFunctionCall(st: S, e: Expr, f: Expr, args: seq<Expr>, st1: S, fv: V, st2: S, argvs: VS)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.FunctionCall? && e.args == [f] + args
    requires !P_Fail(st, e)
    requires P_Succ(st, f, st1, fv)
    requires Pes_Succ(st1, args, st2, argvs)
    requires Pes(st, [f] + args)
    requires !Pes_Fail(st, [f] + args)
    requires Pes_StepValue(st, [f] + args) == AppendValue(fv, argvs)
    ensures P(st, e)

  lemma {:verify false} InductIf_Fail(st: S, e: Expr, cond: Expr, thn: Expr, els: Expr)
    requires e.If? && e.cond == cond && e.thn == thn && e.els == els
    ensures P_Fail(st, cond) ==> P(st, e)

  lemma {:verify false} InductIf_Succ(st: S, e: Expr, cond: Expr, thn: Expr, els: Expr, st_cond: S, condv: V)// st_br: S, brv: V)
    requires e.If? && e.cond == cond && e.thn == thn && e.els == els
    requires !P_Fail(st, e)
    requires P_Succ(st, cond, st_cond, condv)
    requires P(st_cond, thn)
    requires P(st_cond, els)
    ensures P(st, e)

  //
  // Lemmas
  //

  lemma {:verify false} P_Satisfied(st: S, e: Expr)
    ensures P(st, e)
    decreases e, 2
  {
    if P_Fail(st, e) {
      P_Fail_Sound(st, e);
    }
    else {
      P_Satisfied_Succ(st, e);
    }
  }

  function {:verify false} InductExprs_Step(st: S, e0: Expr, i: nat, e: Expr, es: seq<Expr>): (out: (S, V, S, VS))
    requires e0.Apply? // This is for termination
    requires i < |e0.args| // This is for termination
    requires e0.args[i..] == [e] + es // This is for termination
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
    decreases e0, 0
  {
    Pes_Satisfied(st, [e] + es);
    
    assert e == e0.args[i];
    assert e < e0;
    P_Satisfied(st, e); // Recursion
    assert !P_Fail(st, e) ==> Pes(P_StepState(st, e), es) by {
      if !P_Fail(st, e) {
        Pes_Satisfied(P_StepState(st, e), es); // Recursion
      }
    }

    InductExprs_Succ_Impl(st, e, es);

    var (st1, v) := P_Step(st, e);
    var (st2, vs) := Pes_Step(st1, es);

    var (stf, vsf) := Pes_Step(st, [e] + es);
    Pes_Succ_Inj(st, [e] + es, st2, stf, AppendValue(v, vs), vsf);

    (st1, v, st2, vs)
  }

  lemma {:verify true} P_Satisfied_Succ(st: S, e: Expr)
    requires !P_Fail(st, e)
    ensures P(st, e)
    decreases e, 1
  {
    reveal SupportsInterp();
    
    match e {
      case Var(_) =>
        InductVar(st, e);

      case Literal(_) =>
        InductLiteral(st, e);

      case Abs(vars, body) =>
        forall env, argvs | VS_CallStatePre(vars, argvs)
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
        InductApplyLazy(st, e, arg0, arg1);

      case Apply(Eager(aop), _) =>
        Pes_Satisfied(st, e.args); // Recursion

        if Pes_Fail(st, e.args) {
          InductApplyEager_Fail(st, e, e.args);
        }
        else {
          var (st', vs) := Pes_Step(st, e.args);

          match aop
            case UnaryOp(op) =>
              var arg0 := e.args[0];
              assert e.args == [arg0] + [];
              var (st1, v0, st2, vs1) := InductExprs_Step(st, e, 0, arg0, []);

              // Prove that the sequence of arguments evaluates to: [v0]
              var es := [];
              assert Pes_Succ(st1, es, st2, vs1);
              assert st2 == st';
              assert AppendValue(v0, vs1) == vs;
              InductExprs_Nil(st1);
              assert Pes_Succ(st1, es, st1, NilVS);
              Pes_Succ_Inj(st1, es, st1, st2, NilVS, vs1);
              ToSeq_Append(v0, []);
              assert [v0] + [] == [v0];
              assert ToSeq([v0]) == AppendValue(v0, NilVS);
              InductApplyEagerUnaryOp_Succ(st, e, op, arg0, st1, v0);

            case BinaryOp(op) =>
              var arg0 := e.args[0];
              var arg1 := e.args[1];
              assert e.args == [arg0, arg1];

              assert e.args == [arg0] + [arg1];
              var (st1, v0, st2, vs') := InductExprs_Step(st, e, 0, arg0, [arg1]);

              assert [arg1] == [arg1] + [];
              var (st2', v1, st3, vs'') := InductExprs_Step(st1, e, 1, arg1, []);

              // Prove that the sequence of arguments evaluates to: [v0, v1]
              var es := [];
              InductExprs_Nil(st2');
              assert Pes_Succ(st2', es, st2', NilVS);
              Pes_Succ_Inj(st2', es, st2', st3, NilVS, vs'');
              ToSeq_Append(v1, []);
              ToSeq_Append(v0, [v1]);
              assert [v1] + [] == [v1];
              assert [v0] + [v1] == [v0, v1];
              assert ToSeq([v0, v1]) == AppendValue(v0, AppendValue(v1, NilVS));

              InductApplyEagerBinaryOp_Succ(st, e, op, arg0, arg1, st1, v0, st2', v1);

            case TernaryOp(op) =>
              var arg0 := e.args[0];
              var arg1 := e.args[1];
              var arg2 := e.args[2];
              assert e.args == [arg0, arg1, arg2];

              assert e.args == [arg0] + [arg1, arg2];
              var (st1, v0, st2, vs') := InductExprs_Step(st, e, 0, arg0, [arg1, arg2]);

              assert [arg1, arg2] == [arg1] + [arg2];
              var (st2', v1, st3, vs'') := InductExprs_Step(st1, e, 1, arg1, [arg2]);

              assert [arg2] == [arg2] + [];
              var (st3', v2, st4, vs''') := InductExprs_Step(st2', e, 2, arg2, []);

              // Prove that the sequence of arguments evaluates to: [v0, v1]
              var es := [];
              InductExprs_Nil(st3');
              assert Pes_Succ(st3', es, st3', NilVS);
              Pes_Succ_Inj(st3', es, st3', st4, NilVS, vs''');
              ToSeq_Append(v2, []);
              ToSeq_Append(v1, [v2]);
              ToSeq_Append(v0, [v1, v2]);
              assert [v2] + [] == [v2];
              assert [v1] + [v2] == [v1, v2];
              assert [v0] + [v1, v2] == [v0, v1, v2];
              assert ToSeq([v0, v1, v2]) == AppendValue(v0, AppendValue(v1, AppendValue(v2, NilVS)));

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
              var (st1, fv, st2, argvs) := InductExprs_Step(st, e, 0, f, args);

              InductApplyEagerFunctionCall(st, e, f, args, st1, fv, st2, argvs);
        }

      case If(cond, thn, els) =>
        // Recursion
        P_Satisfied(st, cond);

        // Evaluate the condition
        if P_Fail(st, cond) {
          InductIf_Fail(st, e, cond, thn, els);
        }
        else {            
          var (st_cond, condv) := P_Step(st, cond);

          P_Satisfied(st_cond, thn); // Recursion
          P_Satisfied(st_cond, els); // Recursion
          
          InductIf_Succ(st, e, cond, thn, els, st_cond, condv);
        }

      case VarDecl(_, _) =>
        assume false; // TODO: prove

      case Update(_, _) =>
        assume false; // TODO: prove

      case Block(_) =>
        assume false; // TODO: prove
    }
  }

  lemma {:verify false} Pes_Satisfied(st: S, es: seq<Expr>)
    ensures Pes(st, es)
    decreases es, 0
  {
    assume false;
  }
}

module EqInterpRefl refines Ind {
  //
  // Declarations
  //
  type {:verify false} Value = Interp.Value

  datatype {:verify false} MState = MState(env: Environment, ctx: State, ctx': State)
  datatype {:verify false} MValue = MValue(v: Value, v': Value)
  datatype {:verify false} MSeqValue = MSeqValue(vs: seq<Value>, vs': seq<Value>)

  type {:verify false} S(!new) = MState
  type {:verify false} V(!new) = MValue
  type {:verify false} VS(!new) = MSeqValue

  predicate {:verify false} P(st: S, e: Expr)
  {
    EqState(st.ctx, st.ctx') ==>
    EqInterpResultValue(InterpExpr(e, st.env, st.ctx), InterpExpr(e, st.env, st.ctx'))
  }
  
  predicate {:verify false} P_Succ(st: S, e: Expr, st': S, v: V)
  {
    && EqState(st.ctx, st.ctx')
    && EqInterpResultValue(InterpExpr(e, st.env, st.ctx), InterpExpr(e, st.env, st.ctx'))
    && InterpExpr(e, st.env, st.ctx) == Success(Return(v.v, st'.ctx))
    && InterpExpr(e, st.env, st.ctx') == Success(Return(v.v', st'.ctx'))
    && st.env == st'.env
  }

  predicate {:verify false} P_Fail(st: S, e: Expr)
  {
    // TODO: P ==> Q
    !EqState(st.ctx, st.ctx') || InterpExpr(e, st.env, st.ctx).Failure?
  }

  predicate {:verify false} Pes(st: S, es: seq<Expr>)
  {
    EqState(st.ctx, st.ctx') ==>
    EqInterpResultSeqValue(InterpExprs(es, st.env, st.ctx), InterpExprs(es, st.env, st.ctx'))
  }

  predicate {:verify false} Pes_Succ(st: S, es: seq<Expr>, st': S, vs: VS)
  {
    && EqState(st.ctx, st.ctx')
    && EqInterpResultSeqValue(InterpExprs(es, st.env, st.ctx), InterpExprs(es, st.env, st.ctx'))
    && InterpExprs(es, st.env, st.ctx) == Success(Return(vs.vs, st'.ctx))
    && InterpExprs(es, st.env, st.ctx') == Success(Return(vs.vs', st'.ctx'))
    && st.env == st'.env
  }

  predicate {:verify false} Pes_Fail(st: S, es: seq<Expr>)
  {
    !EqState(st.ctx, st.ctx') || InterpExprs(es, st.env, st.ctx).Failure?
  }

  function {:verify false} AppendValue ...
  {
    MSeqValue([v.v] + vs.vs, [v.v'] + vs.vs')
  }

  function {:verify false} ToSeq ...
  {
    if vs == [] then MSeqValue([], [])
    else
      AppendValue(MValue(vs[0].v, vs[0].v'), ToSeq(vs[1..]))
  }
  
  function {:verify false} GetNilVS ...
  {
    MSeqValue([], [])
  }

  predicate VS_CallStatePre ...
  {
    && |argvs.vs| == |argvs.vs'| == |vars|
    && forall i | 0 <= i < |argvs.vs| :: EqValue(argvs.vs[i], argvs.vs'[i])
  }

  function {:verify false} BuildClosureCallState ...
  {
    var ctx1 := BuildCallState(st.ctx.locals, vars, argvs.vs);
    var ctx1' := BuildCallState(st.ctx'.locals, vars, argvs.vs');
    MState(env, ctx1, ctx1')
  }

  function {:verify false} P_Step ... {
    var Return(v, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    var Return(v', ctx1') := InterpExpr(e, st.env, st.ctx').value;
    (MState(st.env, ctx1, ctx1'), MValue(v, v'))
  }

  function {:verify false} Pes_Step ... {
    var Return(vs, ctx1) := InterpExprs(es, st.env, st.ctx).value;
    var Return(vs', ctx1') := InterpExprs(es, st.env, st.ctx').value;
    (MState(st.env, ctx1, ctx1'), MSeqValue(vs, vs'))
  }

  //
  // Lemmas
  //

  lemma {:verify false} P_Fail_Sound ... {}
  lemma {:verify false} P_Succ_Sound ... {}
  lemma {:verify false} Pes_Fail_Sound ... {}
  lemma {:verify false} Pes_Succ_Sound ... {}

  lemma {:verify false} Pes_Succ_Inj ... {}
  lemma {:verify false} ToSeq_Append ... {}

  lemma {:verify false} InductVar ... {
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
    // TODO: post-condition for BuildClosureCallState? (EqState(st) ==> EqState(st'))
    // It seems we only need the call to ``BuildCallState_EqState`` in the forall statement
    reveal InterpExpr();
    reveal EqValue_Closure();

    var MState(env, ctx, ctx') := st;
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
      var argvs := MSeqValue(argvs, argvs');

      var ctx1 := BuildCallState(st.ctx.locals, vars, argvs.vs);
      assert ctx1 == BuildCallState(cv.ctx, cv.vars, argvs.vs);
      var ctx1' := BuildCallState(st.ctx'.locals, vars, argvs.vs');
      assert ctx1' == BuildCallState(cv'.ctx, cv'.vars, argvs.vs');

      BuildCallState_EqState(cv.ctx, cv'.ctx, vars, argvs.vs, argvs.vs'); // We only need this

      var st_cl := MState(env, ctx1, ctx1');
      assert VS_CallStatePre(vars, argvs);
      assert P(BuildClosureCallState(st, vars, body, env, argvs), body);
      assert st_cl == BuildClosureCallState(st, vars, body, env, argvs);

      assert P(st_cl, body);

      BuildCallState_EqState(cv.ctx, cv'.ctx, vars, argvs.vs, argvs.vs');      
      assert EqState(st_cl.ctx, st_cl.ctx');
      assert EqInterpResultValue(InterpExpr(cv.body, env, ctx1), InterpExpr(cv'.body, env, ctx1'));

      reveal InterpCallFunctionBody();
    }

    assert EqValue_Closure(cv, cv');
  }

  lemma {:verify false} InductAbs_CallState ... {
    reveal InterpExpr();
    reveal InterpCallFunctionBody();
    reveal BuildCallState();

    BuildCallState_EqState(st.ctx.locals, st.ctx'.locals, vars, argvs.vs, argvs.vs');
  }

  lemma {:verify false} InductExprs_Nil ... { reveal InterpExprs(); }

  lemma {:verify false} InductExprs_Succ_Impl ... { reveal InterpExprs(); }

  lemma {:verify false} InductApplyLazy ... {
    assume false;
  } // TODO: prove

  lemma {:verify false} InductApplyEager_Fail ... { reveal InterpExpr(); }

  lemma {:verify false} InductApplyEagerUnaryOp_Succ ... { reveal InterpExpr(); reveal InterpUnaryOp(); }

  lemma {:verify false} InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    InterpBinaryOp_Eq(e, e, op, v0.v, v1.v, v0.v', v1.v');
  }

  lemma {:verify false} InductApplyEagerTernaryOp_Succ ... {
    reveal InterpExpr();
    reveal InterpTernaryOp();

    // TODO: using this lemma makes Dafny crash
    // InterpTernaryOp_Eq(e, e, op, v0.v, v1.v, v2.v, v0.v', v1.v', v2.v');

    EqValue_HasEqValue_Eq(v0.v, v0.v');
    EqValue_HasEqValue_Eq(v1.v, v1.v');
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
}

} // end of module Bootstrap.Semantics.ExprInduction


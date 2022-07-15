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

  // We need ``IsTrue`` and ``IsFalse`` (and can't use `!IsTrue(v)` instead of `IsFalse(v)`)
  // because `v` is not necessarily a boolean.
  // DISCUSSION: we don't need those two predicates if we weaken a bit ``InductIf`` by using
  // `P(st_cond, thn)` instead of `P_Succ(st_cond, thn, ...)` for instance.
  predicate {:verify false} IsTrue(v: V)
  predicate {:verify false} IsFalse(v: V) ensures IsFalse(v) ==> !IsTrue(v)

  // TODO: change the lemmas to, for example for if then else:
  // P_Fail(e) ==> OK
  // !P_Fail(e) && P_Succ(cond) && IsTrue(condv) && P_Succ(thn) ==> P_Succ(e)
  // ...
    
//  function CombineValues(v: V, vs: VS): VS // TODO: remove?
//  function UpdateOnAbs(st: S, vars: seq<string>, body: Expr): S // TODO: remove?

  // TODO: change that to a function
  lemma {:verify false} P_ExcludedMiddle(st: S, e: Expr)
    requires P(st, e)
    ensures P_Fail(st, e) || exists st', v :: P_Succ(st, e, st', v)
    ensures P_Fail(st, e) ==> forall st', v :: !P_Succ(st, e, st', v)

  // TODO: change that to a function
  lemma {:verify false} Pes_ExcludedMiddle(st: S, es: seq<Expr>)
    requires Pes(st, es)
    ensures Pes_Fail(st, es) || exists st', vs :: Pes_Succ(st, es, st', vs)
    ensures Pes_Fail(st, es) ==> forall st', vs :: !Pes_Succ(st, es, st', vs)

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

  lemma {:verify false} InductVar(st: S, e: Expr)
    requires e.Var?
    ensures P(st, e)

  lemma {:verify false} InductLiteral(st: S, e: Expr)
    requires e.Literal?
    ensures P(st, e)

  lemma {:verify false} InductAbs(st: S, e: Expr)
    requires e.Abs?
    ensures P(st, e)

/*    lemma InductExprs_Fail(st: S, e: Expr, es: seq<Expr>)
    ensures P_Fail(st, e) ==> Pes(st, [e] + es)
    ensures forall st1, v :: P_Succ(st, e, st1, v) && Pes_Fail(st1, es) ==> Pes(st, [e] + es)
    ensures P_Fail(st, e) ==> Pes(st, [e] + es)

  lemma {:verify false} InductExprs_Succ(st: S, e: Expr, es: seq<Expr>, st1: S, v: V, st2: S, vs: VS)
    requires P_Succ(st, e, st1, v)
    requires Pes_Succ(st1, es, st2, vs)
    ensures Pes(st, [e] + es)
*/

  lemma {:verify false} InductExprs_Nil(st: S)
    ensures Pes(st, [])

  lemma {:verify false} InductExprs_Succ_Impl(st: S, e: Expr, es: seq<Expr>, st': S, vs: VS)
    requires Pes_Succ(st, [e] + es, st', vs) // TODO: change to !Pes_Fail
    requires P(st, e)
    requires forall st :: Pes(st, es) // TODO: use the functions which return witnesses
//    ensures exists st1, v :: 
//    requires forall st1, v :: P_Succ(st, e, st1, v) && Pes_Succ(st1, es, st2, vs')
//    requires forall st :: P(st, e)
//    requires forall st :: Pes(st, es)
    ensures exists st1, v, st2, vs' :: P_Succ(st, e, st1, v) && Pes_Succ(st1, es, st2, vs')

//  lemma InductExprs_Succ_Equiv(st: S, e: Expr, es: seq<Expr>)
//    ensures Pes(st, [e] + es) <==> P_Fail(st, e) || (exists st1, v :: P_Succ(st, e, st1, v) && Pes(st1, es))

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
    ensures P(st, e)

  lemma {:verify false} InductApplyEagerBinaryOp_Succ(st: S, e: Expr, op: BinaryOps.T, arg0: Expr, arg1: Expr, st1: S, v0: V, st2: S, v1: V)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.BinaryOp? && e.aop.eOp.bop == op && e.args == [arg0, arg1]
    requires !P_Fail(st, e)
    requires P_Succ(st, arg0, st1, v0)
    requires P_Succ(st1, arg1, st2, v1)
    ensures P(st, e)

  lemma {:verify false} InductApplyEagerTernaryOp_Succ(st: S, e: Expr, arg0: Expr, arg1: Expr, arg2: Expr, st1: S, v0: V, st2: S, v1: V, st3: S, v2: V)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.TernaryOp? && e.args == [arg0, arg1, arg2]
    requires !P_Fail(st, e)
    requires P_Succ(st, arg0, st1, v0)
    requires P_Succ(st1, arg1, st2, v1)
    requires P_Succ(st2, arg2, st3, v2)
    ensures P(st, e)

  lemma {:verify false} InductApplyEagerBuiltin(st: S, e: Expr) // TODO(SMH): make this more precise
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.Builtin?
    ensures P(st, e)

  lemma {:verify false} InductApplyEagerFunctionCall(st: S, e: Expr, f: Expr, args: seq<Expr>, st1: S, fv: V, st2: S, argvs: VS)
    requires e.Apply? && e.aop.Eager? && e.aop.eOp.FunctionCall? && e.args == [f] + args
    requires !P_Fail(st, e)
    requires P_Succ(st, f, st1, fv)
    requires Pes_Succ(st1, args, st2, argvs)
    ensures P(st, e)

  lemma {:verify false} InductIf_Fail(st: S, e: Expr, cond: Expr, thn: Expr, els: Expr)
    requires e.If? && e.cond == cond && e.thn == thn && e.els == els
    ensures P_Fail(st, cond) ==> P(st, e)
    ensures forall st_cond, condv :: P_Succ(st, cond, st_cond, condv) && !IsTrue(condv) && !IsFalse(condv) ==> P(st, e)
    ensures forall st_cond, condv :: P_Succ(st, cond, st_cond, condv) && IsTrue(condv) && P_Fail(st_cond, thn) ==> P(st, e)
    ensures forall st_cond, condv :: P_Succ(st, cond, st_cond, condv) && IsFalse(condv) && P_Fail(st_cond, els) ==> P(st, e)

  lemma {:verify false} InductIf_Succ(st: S, e: Expr, cond: Expr, thn: Expr, els: Expr, st_cond: S, condv: V, st_br: S, brv: V)
    requires e.If? && e.cond == cond && e.thn == thn && e.els == els
    requires !P_Fail(st, e)
    requires P_Succ(st, cond, st_cond, condv)
    requires IsTrue(condv) || IsFalse(condv)
    requires IsTrue(condv) ==> P_Succ(st_cond, thn, st_br, brv)
    requires IsFalse(condv) ==> P_Succ(st_cond, els, st_br, brv)
    ensures P(st, e)

  //
  // Lemmas
  //

  lemma {:verify false} P_Satisfied(st: S, e: Expr)
    ensures P(st, e)
    decreases e, 1
  {
    if P_Fail(st, e) {
      P_Fail_Sound(st, e);
    }
    else {
      P_Satisfied_Succ(st, e);
    }
  }

  lemma {:verify false} P_Satisfied_Succ(st: S, e: Expr)
    requires !P_Fail(st, e)
    ensures P(st, e)
    decreases e, 0
  {
    reveal SupportsInterp();
    
    match e {
      case Var(_) =>
        InductVar(st, e);

      case Literal(_) =>
        InductLiteral(st, e);

      case Abs(_, _) =>
        InductAbs(st, e);

      case Apply(Lazy(_), _) =>
        var arg0 := e.args[0];
        var arg1 := e.args[1];
        InductApplyLazy(st, e, arg0, arg1);

      case Apply(Eager(aop), _) =>
        // Recursion
        Pes_Satisfied(st, e.args);

        if Pes_Fail(st, e.args) {
          InductApplyEager_Fail(st, e, e.args);
        }
        else {
          Pes_ExcludedMiddle(st, e.args);
          var st': S, vs: VS :| Pes_Succ(st, e.args, st', vs);

          match aop
            case UnaryOp(op) =>
              var arg0 := e.args[0];
              assert e.args == [arg0] + [];
              // TODO: fix (forall quantif)
              InductExprs_Succ_Impl(st, arg0, [], st', vs);
              var st1: S, v0: V :| P_Succ(st, arg0, st1, v0);
              InductApplyEagerUnaryOp_Succ(st, e, op, arg0, st1, v0);

            case BinaryOp(op) =>
              var arg0 := e.args[0];
              var arg1 := e.args[1];
              assert e.args == [arg0, arg1];

              assert e.args == [arg0] + [arg1];
              InductExprs_Succ_Impl(st, arg0, [arg1], st', vs);
              var st1, v0, st2, vs' :| P_Succ(st, arg0, st1, v0) && Pes_Succ(st1, [arg1], st2, vs');

              assert [arg1] == [arg1] + [];
              InductExprs_Succ_Impl(st1, arg1, [], st2, vs');
              var st2', v1, st3, vs'' :| P_Succ(st1, arg1, st2', v1) && Pes_Succ(st2', [], st3, vs'');

              InductApplyEagerBinaryOp_Succ(st, e, op, arg0, arg1, st1, v0, st2', v1);

            case TernaryOp(_) =>
              var arg0 := e.args[0];
              var arg1 := e.args[1];
              var arg2 := e.args[2];
              assert e.args == [arg0, arg1, arg2];

              assert e.args == [arg0] + [arg1, arg2];
              InductExprs_Succ_Impl(st, arg0, [arg1, arg2], st', vs);
              var st1, v0, st2, vs' :| P_Succ(st, arg0, st1, v0) && Pes_Succ(st1, [arg1, arg2], st2, vs');

              assert [arg1, arg2] == [arg1] + [arg2];
              InductExprs_Succ_Impl(st1, arg1, [arg2], st2, vs');
              var st2', v1, st3, vs'' :| P_Succ(st1, arg1, st2', v1) && Pes_Succ(st2', [arg2], st3, vs'');

              assert [arg2] == [arg2] + [];
              InductExprs_Succ_Impl(st2', arg2, [], st3, vs'');
              var st3', v2, st4, vs''' :| P_Succ(st2', arg2, st3', v2) && Pes_Succ(st3', [], st4, vs''');

              InductApplyEagerTernaryOp_Succ(st, e, arg0, arg1, arg2, st1, v0, st2', v1, st3', v2);

            case Builtin(_) =>
              InductApplyEagerBuiltin(st, e);

            case FunctionCall =>
              var f := e.args[0];
              var args := e.args[1..];

              assert e.args == [f] + args;
              InductExprs_Succ_Impl(st, f, args, st', vs);

              var st1, fv, st2, argvs :| P_Succ(st, f, st1, fv) && Pes_Succ(st1, args, st2, argvs);

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
          P_ExcludedMiddle(st, cond);
          var st_cond, condv :| P_Succ(st, cond, st_cond, condv);

          // Test the condition
          if IsTrue(condv) {
            P_Satisfied(st_cond, thn); // Recursion
            P_ExcludedMiddle(st_cond, thn);

            if P_Fail(st_cond, thn) {
              InductIf_Fail(st, e, cond, thn, els);
            }
            else {
              var st_br, brv :| P_Succ(st_cond, thn, st_br, brv);

              //Recursion
              P_Satisfied(st_cond, thn);

              // Success case
              InductIf_Succ(st, e, cond, thn, els, st_cond, condv, st_br, brv);
            }
          }
          else if IsFalse(condv) {
            P_Satisfied(st_cond, els); // Recursion
            P_ExcludedMiddle(st_cond, els);

            if P_Fail(st_cond, els) {
              InductIf_Fail(st, e, cond, thn, els);
            }
            else {
              var st_br, brv :| P_Succ(st_cond, els, st_br, brv);

              //Recursion
              P_Satisfied(st_cond, els);

              // Success case
              InductIf_Succ(st, e, cond, thn, els, st_cond, condv, st_br, brv);
            }
          }
          else {
            InductIf_Fail(st, e, cond, thn, els);
          }
        }

      case VarDecl(_, _) =>
        assume false;

      case Update(_, _) =>
        assume false;

      case Block(_) =>
        assume false;
    }
  }

  lemma {:verify false} Pes_Satisfied(st: S, es: seq<Expr>)
    ensures Pes(st, es)
    decreases es
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

  predicate {:verify false} IsTrue ...
  {
    v.v.Bool? && v.v.b
  }
  predicate {:verify false} IsFalse ...
  {
    v.v.Bool? && !v.v.b
  }

  
  //
  // Lemmas
  //
  
  lemma {:verify false} P_ExcludedMiddle ... {
    // Damn, Z3 is bad at instantiating existential quantifiers
    if EqState(st.ctx, st.ctx') && InterpExpr(e, st.env, st.ctx).Success? {
      var Return(v, ctx1) := InterpExpr(e, st.env, st.ctx).value;
      var Return(v', ctx1') := InterpExpr(e, st.env, st.ctx').value;
      assert P_Succ(st, e, MState(st.env, ctx1, ctx1'), MValue(v, v'));
    }
    else {}
  }

  lemma {:verify false} Pes_ExcludedMiddle ... {
    // Damn, Z3 is bad at instantiating existential quantifiers
    if EqState(st.ctx, st.ctx') && InterpExprs(es, st.env, st.ctx).Success? {
      var Return(vs, ctx1) := InterpExprs(es, st.env, st.ctx).value;
      var Return(vs', ctx1') := InterpExprs(es, st.env, st.ctx').value;
      assert Pes_Succ(st, es, MState(st.env, ctx1, ctx1'), MSeqValue(vs, vs'));
    }
    else {}
  }

  lemma {:verify false} P_Fail_Sound ... {}
  lemma {:verify false} P_Succ_Sound ... {}
  lemma {:verify false} Pes_Fail_Sound ... {}
  lemma {:verify false} Pes_Succ_Sound ... {}

  lemma {:verify false} InductVar ... { assume false; }
  lemma {:verify false} InductLiteral ... { assume false; }
  lemma {:verify false} InductAbs ... { assume false; }

  lemma {:verify false} InductExprs_Nil ... { reveal InterpExprs(); }

  lemma {:verify false} InductExprs_Succ_Impl ... {
    reveal InterpExprs();

    assert Pes_Succ(st, [e] + es, st', vs);

    assert ([e] + es)[0] == e;
    assert ([e] + es)[1..] == es;
    
    var Return(v, ctx1) := InterpExpr(e, st.env, st.ctx).value;
    var Return(v', ctx1') := InterpExpr(e, st.env, st.ctx').value;

    var v1 := MValue(v, v');
    var st1 := MState(st.env, ctx1, ctx1');

    assert P_Succ(st, e, st1, v1);

    var Return(vs, ctx2) := InterpExprs(es, st.env, ctx1).value;
    var Return(vs', ctx2') := InterpExprs(es, st.env, ctx1').value;

    var st2 := MState(st.env, ctx2, ctx2');
    var vs2 := MSeqValue(vs, vs');
    assert Pes(st1, es); // We need this
    assert Pes_Succ(st1, es, st2, vs2);
  }

  lemma {:verify false} InductApplyLazy ... { assume false; }
  lemma {:verify false} InductApplyEager_Fail ... { reveal InterpExpr(); }

  lemma {:verify false} InductApplyEagerUnaryOp_Succ ... {
    reveal InterpExpr();
    reveal InterpUnaryOp();

    var ares := InterpExprs(e.args, st.env, st.ctx);
    var ares' := InterpExprs(e.args, st.env, st.ctx);

    assume ares.Success?;
    assume ares'.Success?;
    assume ares == Success(Return([v0.v], st1.ctx));
    assume ares' == Success(Return([v0.v'], st1.ctx'));
  }

  lemma {:verify false} InductApplyEagerBinaryOp_Succ ... {
    reveal InterpExpr();
    reveal InterpBinaryOp();

    assert InterpExpr(arg0, st.env, st.ctx) == Success(Return(v0.v, st1.ctx));
    assert InterpExpr(arg0, st.env, st.ctx') == Success(Return(v0.v', st1.ctx'));

    assert InterpExpr(arg1, st1.env, st1.ctx) == Success(Return(v1.v, st2.ctx));
    assert InterpExpr(arg1, st1.env, st1.ctx') == Success(Return(v1.v', st2.ctx'));

    var ares := InterpExprs(e.args, st.env, st.ctx);
    var ares' := InterpExprs(e.args, st.env, st.ctx);

    // TODO
    assume ares.Success?;
    assume ares'.Success?;
    assume ares == Success(Return([v0.v, v1.v], st2.ctx));
    assume ares' == Success(Return([v0.v', v1.v'], st2.ctx'));

    assume !P_Fail(st, e); // TODO

    assert EqValue(v0.v, v0.v');
    assert EqValue(v1.v, v1.v');

    EqValue_HasEqValue_Eq(v0.v, v0.v');
    EqValue_HasEqValue_Eq(v1.v, v1.v');

//    assume false;

    match op
      case Numeric(op) =>
        assume false; // TODO: prove
      case Logical(op) =>
        assume false;
      case Eq(op) =>
        assume false;
      case Char(op) =>
        assume false;
      case Sets(op) =>
        assume false;
      case Multisets(op) =>
        assume false;
      case Sequences(op) =>
        assume false;
      case Maps(op) =>
        assume false;
  }

  lemma {:verify false} InductApplyEagerTernaryOp_Succ ... { assume false; }
  lemma {:verify false} InductApplyEagerBuiltin ... { assume false; }
  lemma {:verify false} InductApplyEagerFunctionCall ... { assume false; }

  lemma {:verify false} InductIf_Fail ... { reveal InterpExpr(); }
  lemma {:verify false} InductIf_Succ ... { reveal InterpExpr(); }
}

} // end of module Bootstrap.Semantics.ExprInduction

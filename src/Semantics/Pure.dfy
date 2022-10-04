include "../Interop/CSharpDafnyModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "Interp.dfy"
include "../Transforms/Generic.dfy"
include "../Transforms/Shallow.dfy"

module Bootstrap.Semantics.Pure {
  // This module defines a notion of pure expression, and proves properties about it (for instance,
  // evaluating a pure expression leaves the state unchanged).

  import Utils.Lib
  import Utils.Lib.Debug
  import opened AST.Syntax
  import opened Utils.Lib.Datatypes

  import opened AST.Predicates
  import opened Interp
  import opened Values

  type Expr = Interp.Expr

  predicate method IsPure_Single(e: Syntax.Expr)
  {
    match e
      case Var(_) => true
      case Literal(_) => true
      case Abs(_, _) => true
      case Apply(aop, _) =>
        match aop {
          case Lazy(lOp) => true
          case Eager(eOp) =>
            match eOp {
              case UnaryOp(_) => true
              case BinaryOp(_) => true
              case TernaryOp(_) => true
              case Builtin(Display(_)) => true
              case Builtin(Predicate(_)) => false // TODO(AAT): support this eventually
              case Builtin(Print) => false // For now, we actually don't model the fact that `Print` has side effects
              case FunctionCall() => true // TODO(SMH): ok for now because we only have terminating, pure functions
              case DataConstructor(_, _) => true
            }
        }
      case Block(_) => true
      case Bind(_, _, _) => true
      case If(_, _, _) => true
      case Unsupported(_, _) => false
  }

  predicate method {:opaque} IsPure(e: Syntax.Expr) {
    Predicates.Deep.All_Expr(e, IsPure_Single)
  }

  // BUG(https://github.com/dafny-lang/dafny/issues/2253)
  type PureExpr = e: Syntax.Expr | SupportsInterp(e) && IsPure(e)
    witness (reveal SupportsInterp(); reveal IsPure(); Expr.Literal(Exprs.Literal.LitUnit))

  predicate InterpResultHasState<T>(res: InterpResult<T>, ctx: State)
  {
    res.Success? ==> res.value.ctx == ctx
  }

  lemma InterpExpr_IsPure_SameState(e: PureExpr, env: Environment, ctx: State)
    ensures InterpResultHasState(InterpExpr(e, env, ctx), ctx)
    decreases e, 2
    // Evaluating a pure expression leaves the state unchanged
  {
    reveal IsPure();
    reveal InterpExpr();
    match e
      case Var(v) =>
      case Abs(vars, body) => {}
      case Literal(lit) => {}
      case Unsupported(_, _) => {}
      case Apply(Lazy(op), args) =>
        InterpExpr_Lazy_IsPure_SameState(e, env, ctx);
      case Apply(Eager(op), args) =>
        InterpExpr_Eager_IsPure_SameState(e, env, ctx);
      case Bind(vars, exprs, body) =>
        assume false; // TODO: prove
      case Block(stmts) =>
        InterpExpr_Block_IsPure_SameState(e, env, ctx);
      case If(cond, thn, els) =>
        InterpExpr_If_IsPure_SameState(e, env, ctx);
  }

  lemma InterpExprWithType_IsPure_SameState(e: PureExpr, ty: Type, env: Environment, ctx: State)
    ensures InterpResultHasState(InterpExprWithType(e, ty, env, ctx), ctx)
    decreases e, 3
  {
    reveal SupportsInterp();
    reveal InterpExpr();
    reveal IsPure();

    InterpExpr_IsPure_SameState(e, env, ctx);
  }

  lemma InterpExpr_Lazy_IsPure_SameState(e: PureExpr, env: Environment, ctx: State)
    requires e.Apply? && e.aop.Lazy?
    ensures InterpResultHasState(InterpExpr(e, env, ctx), ctx)
    decreases e, 0
  {
    reveal SupportsInterp();
    reveal InterpExpr();
    reveal IsPure();
    reveal InterpLazy();
    
    var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
    var res0 := InterpExprWithType(e0, Type.Bool, env, ctx);
    if res0.Success? {
      var Return(v0, ctx0) := res0.value;

      InterpExprWithType_IsPure_SameState(e0, Type.Bool, env, ctx);
      InterpExprWithType_IsPure_SameState(e1, Type.Bool, env, ctx);
    }
    else {}
  }

  lemma InterpExpr_Eager_IsPure_SameState(e: PureExpr, env: Environment, ctx: State)
    requires e.Apply? && e.aop.Eager?
    ensures InterpResultHasState(InterpExpr(e, env, ctx), ctx)
    decreases e, 0
  {
    reveal SupportsInterp();
    reveal InterpExpr();
    reveal IsPure();
    reveal InterpLazy();

    var op := e.aop.eOp;
    var args := e.args;

    InterpExprs_IsPure_SameState(args, env, ctx);
  }

  lemma InterpExpr_Block_IsPure_SameState(e: PureExpr, env: Environment, ctx: State)
    requires e.Block?
    ensures InterpResultHasState(InterpExpr(e, env, ctx), ctx)
    decreases e, 1
  {
    reveal SupportsInterp();
    reveal InterpExpr();
    reveal IsPure();
    reveal InterpBlock();

    InterpBlock_Exprs_IsPure_SameState(e.stmts, env, ctx);
  }

  lemma InterpBlock_Exprs_IsPure_SameState(es: seq<PureExpr>, env: Environment, ctx: State)
    ensures InterpResultHasState(InterpBlock_Exprs(es, env, ctx), ctx)
    decreases es, 0
  {
    reveal IsPure();
    reveal InterpBlock_Exprs();

    if es == [] {}
    else if |es| == 1 {
      InterpExpr_IsPure_SameState(es[0], env, ctx);
    }
    else {
      var res0 := InterpExpr(es[0], env, ctx);
      if res0.Success? {
        InterpExpr_IsPure_SameState(es[0], env, ctx);
        InterpBlock_Exprs_IsPure_SameState(es[1..], env, ctx);
      }
      else {}
    }
  }

  lemma InterpExpr_If_IsPure_SameState(e: PureExpr, env: Environment, ctx: State)
    requires e.If?
    ensures InterpResultHasState(InterpExpr(e, env, ctx), ctx)
    decreases e, 0
  {
    reveal SupportsInterp();
    reveal InterpExpr();
    reveal IsPure();

    var If(cond, thn, els) := e;
    InterpExpr_IsPure_SameState(cond, env, ctx);
    InterpExpr_IsPure_SameState(thn, env, ctx);
    InterpExpr_IsPure_SameState(els, env, ctx);
  }

  lemma InterpExprs_IsPure_SameState(es: seq<PureExpr>, env: Environment, ctx: State)
    ensures InterpResultHasState(InterpExprs(es, env, ctx), ctx)
    decreases es, 1
  {
    reveal InterpExprs();
    if es == [] {}
    else {
      InterpExpr_IsPure_SameState(es[0], env, ctx);
      InterpExprs_IsPure_SameState(es[1..], env, ctx);
    }
  }
}

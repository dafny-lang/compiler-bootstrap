include "Utils.dfy"
include "AST.dfy"

module Interp {
  import opened Utils
  import opened AST

  type Context = map<string, int>

  type InterpResult = Result<(int, Context)>

  function method InterpBinOp(op: BinOp, x: int, y: int): int
  {
    match op
      case Add => x + y
      case Sub => x - y
      case Mul => x * y
  }

  function method InterpExpr(e: Expr, ctx: Context): Result<(int, Context)> {
    match e {
      case Var(name) =>
        if name in ctx.Keys then Success((ctx[name], ctx)) else Failure

      case Literal(n) =>
        Success((n, ctx))

      case Bind(bvar, bval, body) =>
        var (bvalv, ctx1) :- InterpExpr(bval, ctx);
        var ctx2 := ctx1[bvar := bvalv];
        var (bodyv, ctx3) :- InterpExpr(body, ctx2);
        var ctx4 := ctx1 + (ctx3 - {bvar});
        Success((bodyv, ctx4))

      case Assign(avar, aval) =>
        var (v, ctx1) :- InterpExpr(aval, ctx);
        // We could check that `avar in ctx1.Keys`, but if we do so the assignment we
        // do here is not the same as for ``Bind`` (and may fail) which is annoying
        // for the proofs.
        Success((0, ctx1[avar := v]))

      case If(cond, thn, els) =>
        var (condv, ctx_cond) :- InterpExpr(cond, ctx);
        if condv != 0 then
          InterpExpr(thn, ctx_cond)
        else
          InterpExpr(els, ctx_cond)

      case Op(op, e1, e2) =>
        var (v1, ctx1) :- InterpExpr(e1, ctx);
        var (v2, ctx2) :- InterpExpr(e2, ctx1);
        Success((InterpBinOp(op, v1, v2), ctx2))

      case Seq(e1, e2) =>
        var (_, ctx1) :- InterpExpr(e1, ctx);
        InterpExpr(e2, ctx1)
    }
  }
}

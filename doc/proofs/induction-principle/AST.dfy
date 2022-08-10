include "Utils.dfy"

module AST {
  import opened Utils

  datatype BinOp =
    | Add
    | Sub
    | Mul
  
  datatype Expr =
    | Var(name: string)
    | Literal(n: int)
    | Bind(bvar: string, bval: Expr, body: Expr)
    | Assign(avar: string, aval: Expr)
    | If(cond: Expr, thn: Expr, els: Expr)
    | Op(op: BinOp, oe1: Expr, oe2: Expr)
    | Seq(es: seq<Expr>)
  {
    function method Depth() : nat
    {
      1 + match this {
        case Var(_) =>
          0
        case Literal(lit) =>
          0
        case Bind(bvar, bval, body) =>
          Max(bval.Depth(), body.Depth())
        case Assign(avar, aval) =>
          aval.Depth()
        case If(cond, thn, els) =>
          Max(cond.Depth(), Max(thn.Depth(), els.Depth()))
        case Op(op, e1, e2) =>
          Max(e1.Depth(), e2.Depth())
        case Seq(es: seq<Expr>) =>
          MaxF(var f := (e: Expr) requires e in es => e.Depth(); f, es, 0)
      }
    }
  }
}

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

  type Environment = Interp.Environment
  type State = Interp.State
  type Expr = Interp.Expr

  function method {:opaque} SeqToSet<T>(s: seq<T>): set<T>
    // Unfortunately, we need this small opaque helper to prevent with proof explosions.
  {
    set x | x in s
  }

  function method {:opaque} VarsToNameSet(vars: seq<Exprs.TypedVar>): set<string>
    // Same as for ``SeqToSet``: making this definition opaque is annoying, but we need it to
    // prevent proof explosions.
  {
    set x | x in vars :: x.name
  }

  // TODO(SMH): move?
  function method VarsOfExpr(read: bool, e: Syntax.Expr): set<string>
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

  function method VarsOfExprs(read: bool, es: seq<Syntax.Expr>): set<string>
    decreases Expr.Exprs_Size(es), 1
  {
    if es == [] then {}
    else VarsOfExpr(read, es[0]) + VarsOfExprs(read, es[1..])
  }

  function method UpdtVarsOfExpr(e: Syntax.Expr): set<string>
  {
    VarsOfExpr(false, e)
  }

  function method UpdtVarsOfExprs(es: seq<Syntax.Expr>): set<string>
  {
    VarsOfExprs(false, es)
  }

  function method AllVarsOfExpr(e: Syntax.Expr): set<string>
  {
    VarsOfExpr(true, e)
  }

  function method AllVarsOfExprs(es: seq<Syntax.Expr>): set<string>
  {
    VarsOfExprs(true, es)
  }

  // Accumulator used for substitutions.
  // `subst`: the substitution
  // `frozen`: the variables which appear in the expressions with which we substitute
  datatype SubstAcc = SubstAcc(subst: map<string, Expr>)//, frozen: set<string>)

  predicate method NotVarDecl(e: Syntax.Expr)
  {
    !e.VarDecl?
  }
}

// Rem.(SMH): about the name, see the comment for `Bootstrap.Transforms.VarsOfExpr`
module Bootstrap.Transforms.VarsOfExprUselessBindings.Base {
  // This module proves that:
  // If:
  // - we have an expression `e` and contexts `ctx` and `ctx'`
  // - `ctx'` is `ctx` augmented with bindings which don't appear in `e`
  // Then:
  // - evaluating `e` starting from `ctx` and `ctx'` leads to similar results

  
}

include "Entities.dfy"
include "Syntax.dfy"

module Bootstrap.AST.Predicates {
module Shallow {
  import opened Utils.Lib
  import opened Entities
  import opened Syntax

  function method All_Callable(c: Callable, P: Expr -> bool) : bool {
    && Seq.All(P, c.req)
    && Seq.All(P, c.ens)
    && c.body.All(P)
  }

  function method All_Entity(e: Entity, P: Expr -> bool) : bool {
    match e {
      case Definition(_, d) => d.Callable? ==> All_Callable(d.ci, P)
      // TODO: add fields once they contain expressions
      case _ => true
    }
  }

  function method All_Program(p: Program, P: Expr -> bool) : (r: bool)
  {
    forall e | e in p.registry.entities.Values :: All_Entity(e, P)
  }

  function method All(p: Program, P: Expr -> bool) : bool {
    All_Program(p, P)
  }
}

module DeepImpl {
abstract module Base {
  import opened Utils.Lib
  import opened Entities
  import opened Syntax
  import Shallow

  //
  // Functions
  //

  function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool
    decreases e.Depth(), 0

  function method All_Expr(e: Expr, P: Expr -> bool)
    : (b: bool)
    decreases e.Depth(), 1

  function method Any_Expr(e: Expr, P: Expr -> bool)
    : (b: bool)
    decreases e.Depth(), 1
  {
    !All_Expr(e, e' => !P(e'))
  }

  function method All_Entity(ent: Entity, P: Expr -> bool) : bool {
    Shallow.All_Entity(ent, e => All_Expr(e, P))
  }

  function method All_Program(p: Program, P: Expr -> bool) : bool {
    Shallow.All_Program(p, e => All_Expr(e, P))
  }

  //
  // Lemmas
  //

  // This lemma allows callers to force one level of unfolding of All_Expr
  lemma AllImpliesChildren(e: Expr, p: Expr -> bool)
    requires All_Expr(e, p)
    ensures AllChildren_Expr(e, p)

  lemma AllChildren_Expr_weaken(e: Exprs.T, P: Exprs.T -> bool, Q: Exprs.T -> bool)
    requires AllChildren_Expr(e, P)
    requires forall e' :: P(e') ==> Q(e')
    decreases e, 0
    ensures AllChildren_Expr(e, Q)

  lemma All_Expr_weaken(e: Exprs.T, P: Exprs.T -> bool, Q: Exprs.T -> bool)
    requires All_Expr(e, P)
    requires forall e' :: P(e') ==> Q(e')
    decreases e, 1
    ensures All_Expr(e, Q)

  lemma All_Expr_True(e: Expr, f: Expr -> bool)
    requires forall e :: f(e)
    ensures All_Expr(e, f)
    decreases e, 1

  lemma AllChildren_Expr_True(e: Expr, f: Expr -> bool)
    requires forall e :: f(e)
    ensures AllChildren_Expr(e, f)
    decreases e, 0

  lemma All_Expr_True_Forall(f: Expr -> bool)
    requires forall e :: f(e)
    ensures forall e :: All_Expr(e, f)
}

  module Rec refines Base { // DISCUSS
    function method All_Expr(e: Expr, P: Expr -> bool) : (b: bool) {
      P(e) &&
      // BUG(https://github.com/dafny-lang/dafny/issues/2107)
      // BUG(https://github.com/dafny-lang/dafny/issues/2109)
      // Duplicated to avoid mutual recursion with AllChildren_Expr
      match e {
        case Var(_) => true
        case Literal(lit) => true
        case Abs(vars, body) => All_Expr(body, P)
        case Apply(_, exprs) =>
          Seq.All(e requires e in exprs => All_Expr(e, P), exprs)
        case Block(exprs) =>
          Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
        case Bind(vars, vals, body) =>
          && Seq.All((e requires e in vals => All_Expr(e, P)), vals)
          && All_Expr(body, P)
        case If(cond, thn, els) =>
          All_Expr(cond, P) && All_Expr(thn, P) && All_Expr(els, P)
        case Unsupported(_, exprs) =>
          Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
      }
    }

    function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool {
      match e {
        case Var(_) => true
        case Literal(lit) => true
        case Abs(vars, body) => All_Expr(body, P)
        case Apply(_, exprs) =>
          Seq.All(e requires e in exprs => All_Expr(e, P), exprs)
        case Block(exprs) =>
          Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
        case Bind(vars, vals, body) =>
          && Seq.All((e requires e in vals => All_Expr(e, P)), vals)
          && All_Expr(body, P)
        case If(cond, thn, els) =>
          All_Expr(cond, P) && All_Expr(thn, P) && All_Expr(els, P)
        case Unsupported(_, exprs) =>
          Seq.All((e requires e in exprs => All_Expr(e, P)), exprs)
      }
    }

    lemma AllImpliesChildren ... {}

    lemma All_Expr_weaken ... {
      AllChildren_Expr_weaken(e, P, Q);
    }

    lemma AllChildren_Expr_weaken ... { // NEAT
      forall e' | e' in e.Children() { All_Expr_weaken(e', P, Q); }
    }

    lemma All_Expr_True ... {
      AllChildren_Expr_True(e, f);
    }

    lemma AllChildren_Expr_True ... {
      forall e' | e' in e.Children() { All_Expr_True(e', f); }
    }

    lemma All_Expr_True_Forall ... {
      forall e ensures All_Expr(e, f) {
        All_Expr_True(e, f);
      }
    }

  }

module NonRec refines Base {
  // BUG(https://github.com/dafny-lang/dafny/issues/2107)
  // BUG(https://github.com/dafny-lang/dafny/issues/2109)
  function method All_Expr(e: Expr, P: Expr -> bool) : (b: bool) {
    P(e) && forall e' | e' in e.Children() :: All_Expr(e', P)
  }

  function method AllChildren_Expr(e: Expr, P: Expr -> bool) : bool {
    forall e' | e' in e.Children() :: All_Expr(e', P)
  }

  lemma AllImpliesChildren ... {}

  lemma AllChildren_Expr_weaken ... {
    forall e' | e' in e.Children() { All_Expr_weaken(e', P, Q); }
  }

  lemma All_Expr_weaken ... {
    AllChildren_Expr_weaken(e, P, Q);
  }

  lemma All_Expr_True ... {
    AllChildren_Expr_True(e, f);
  }

  lemma AllChildren_Expr_True ... {
    forall e' | e' in e.Children() { All_Expr_True(e', f); }
  }

  lemma All_Expr_True_Forall ... {
    forall e ensures All_Expr(e, f) {
      All_Expr_True(e, f);
    }
  }

}

module Equiv {
  import Rec
  import NonRec
  import opened Syntax

  lemma AllChildren_Expr(e: Expr, P: Expr -> bool)
    decreases e.Depth(), 0
    ensures Rec.AllChildren_Expr(e, P) == NonRec.AllChildren_Expr(e, P)
  {
    forall e' | e' in e.Children() { All_Expr(e', P); }
  }

  lemma All_Expr(e: Expr, P: Expr -> bool)
    decreases e.Depth(), 1
    ensures Rec.All_Expr(e, P) == NonRec.All_Expr(e, P)
  {
    AllChildren_Expr(e, P);
  }
}
}

  // Both implementations of Deep should work, but NonRec can be somewhat
  // simpler to work with.  If needed, use ``DeepImpl.Equiv.All_Expr`` to
  // switch between implementations.
module Deep refines DeepImpl.NonRec {}
}

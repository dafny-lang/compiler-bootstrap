include "Entities.dfy"
include "Syntax.dfy"

module Bootstrap.AST.Predicates {
module Shallow {
  import opened Utils.Lib.Datatypes
  import Utils.Lib.Outcome.OfSeq
  import opened Entities
  import opened Syntax

  function method All_Entity(ent: Entity, P: Expr -> bool) : bool {
    Seq.All(P, ent.Exprs())
  }

  function method All_Program(p: Program, P: Expr -> bool) : bool {
    Seq.All(P, p.Exprs())
  }
}

module DeepImpl {
abstract module Base {
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

  function method LiftAll_(P: Expr -> bool) : Expr -> bool {
    e => All_Expr(e, P)
  }

  function method All_Entity(ent: Entity, P: Expr -> bool) : bool {
    Shallow.All_Entity(ent, LiftAll_(P))
  }

  function method All_Program(p: Program, P: Expr -> bool) : bool {
    Shallow.All_Program(p, LiftAll_(P))
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

// DISCUSS: Add a fully non-recursive version of Base (with `All_Expr` defined
// as `forall e <- e.SubExpressions() :: P(e)`?

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
}

module Bootstrap.AST.Predicates.Deep refines DeepImpl.NonRec
  // Both implementations of Deep should work, but NonRec can be somewhat
  // simpler to work with.  If needed, use ``DeepImpl.Equiv.All_Expr`` to
  // switch between implementations.
{
  import opened Utils.Lib.Datatypes
  import Utils.Lib.Seq
  import Utils.Lib.Outcome.OfSeq

  function method {:opaque} AllChildren_Expr_Outcome<E>(e: Expr, P: Expr -> Outcome<E>)
    : (os: Outcome<seq<E>>)
    decreases e.Depth(), 0
    ensures os.Pass? <==> AllChildren_Expr(e, OfSeq.Squash(P))
  {
    var children := e.Children();
    var os := OfSeq.AllSeq(children, e' requires e' in children => All_Expr_Outcome(e', P));
    calc <==> {
      AllChildren_Expr(e, OfSeq.Squash(P));
      forall e' | e' in e.Children() :: All_Expr(e', OfSeq.Squash(P));
      forall e' | e' in e.Children() :: All_Expr_Outcome(e', P).Pass?;
      os.Pass?;
    }
    os
  }

  function method {:opaque} All_Expr_Outcome<E>(e: Expr, P: Expr -> Outcome<E>)
    : (os: Outcome<seq<E>>)
    decreases e.Depth(), 1
    ensures os.Pass? <==> All_Expr(e, OfSeq.Squash(P))
  {
    var children := e.Children();
    OfSeq.Cons(P(e), AllChildren_Expr_Outcome(e, P))
  }

  function method {:opaque} All_Entity_Outcome<E>(ent: Entity, P: Expr -> Outcome<E>)
    : (os: Outcome<seq<E>>)
    ensures os.Pass? <==> All_Entity(ent, OfSeq.Squash(P))
  {
    var os := OfSeq.AllSeq(ent.Exprs(), e => All_Expr_Outcome(e, P));
    calc <==> {
      All_Entity(ent, OfSeq.Squash(P));
      Shallow.All_Entity(ent, LiftAll_(OfSeq.Squash(P)));
      Seq.All(e => All_Expr(e, OfSeq.Squash(P)), ent.Exprs());
      Seq.All(e => All_Expr_Outcome(e, P).Pass?, ent.Exprs());
      os.Pass?;
    }
    os
  }

  function method {:opaque} All_Program_Outcome<E>(p: Program, P: Expr -> Outcome<E>)
    : (os: Outcome<seq<E>>)
    ensures os.Pass? <==> All_Program(p, OfSeq.Squash(P))
  {
    var os := OfSeq.AllSeq(p.Exprs(), e => All_Expr_Outcome(e, P));
    calc <==> {
      All_Program(p, OfSeq.Squash(P));
      Shallow.All_Program(p, LiftAll_(OfSeq.Squash(P)));
      Seq.All(e => All_Expr(e, OfSeq.Squash(P)), p.Exprs());
      Seq.All(e => All_Expr_Outcome(e, P).Pass?, p.Exprs());
      os.Pass?;
    }
    os
  }
}

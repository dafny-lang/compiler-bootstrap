include "../AST/Syntax.dfy"

module Bootstrap.Transforms.Generic {
  import opened AST.Syntax

  function IsMap<T(!new), T'>(f: T --> T') : T' -> bool {
    y => exists x | f.requires(x) :: y == f(x)
  }

  lemma Map_All_IsMap<A, B>(f: A --> B, xs: seq<A>)
    requires forall a | a in xs :: f.requires(a)
    ensures Seq.All(IsMap(f), Seq.Map(f, xs))
  {}

  datatype Transformer_<!A(!new), !B> = // FIXME(CPC): Remove rel
    TR(f: A --> B, ghost post: B -> bool)
  {
    predicate HasValidPost() {
      forall a: A | f.requires(a) :: post(f(a))
    }

    predicate HasValidRel(rel: (A,B) -> bool) {
      forall a: A | f.requires(a) :: rel(a, f(a))
    }

    predicate Valid?() {
      forall a | f.requires(a) :: HasValidPost()
    }
  }

  // TODO(SMH): remove?
  function method Comp<A(!new),B,C>(f: A --> B, g: B --> C): (A --> C)
    requires forall x | f.requires(x) :: g.requires(f(x))
    // Compose two transformations
  {
    x requires f.requires(x) => g(f(x))
  }

  type Transformer<!A(!new), !B> = tr: Transformer_<A, B> | tr.Valid?()
    witness *

  type ExprTransformer = Transformer<Expr, Expr>
}

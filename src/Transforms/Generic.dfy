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

    // FIXME(CPC): Move
    predicate All_Rel_Forall<A, B>(rel: (A,B) -> bool, xs: seq<A>, ys: seq<B>)
    {
      && |xs| == |ys|
      && forall i | 0 <= i < |xs| :: rel(xs[i], ys[i])
    }

    datatype Transformer_<!A(!new), !B> = // FIXME(CPC): Remove rel
      TR(f: A --> B, ghost post: B -> bool, ghost rel: (A,B) -> bool)
    {
      predicate HasValidPost() {
        forall a: A | f.requires(a) :: post(f(a))
      }

      predicate HasValidRel() {
        forall a: A | f.requires(a) :: rel(a, f(a))
      }

      predicate Valid?() {
        forall a | f.requires(a) :: HasValidPost() && HasValidRel()
      }
    }

    type Transformer<!A(!new), !B> = tr: Transformer_<A, B> | tr.Valid?()
      witness *

    type ExprTransformer = Transformer<Expr, Expr>
}
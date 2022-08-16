module {:options "-functionSyntax:4"} Bootstrap.AST.Names {
  type Atom =
    // An individual component of a Dafny name.
    s: string | s != "" && '.' !in s witness "n"

  datatype Name =
    | Anonymous
    | Name(parent: Name, suffix: Atom)
  {
    function Length(): nat {
      match this
        case Anonymous => 0
        case Name(_, _) => 1 + parent.Length()
    }

    function ToString(): string {
      match this
        case Anonymous => "_"
        case Name(Anonymous, suffix) => suffix
        case Name(parent, suffix) => parent.ToString() + "." + suffix
    }

    predicate ChildOf(parent: Name)
      // Check whether `this` is a direct descendant of `parent`.
      ensures ChildOf(parent) ==> Length() == parent.Length() + 1
    {
      this.Name? && parent == this.parent
    }

    predicate StrictSuffixOf(parent: Name)
      // Check whether one of the parents of `this` is `parent`.
      ensures StrictSuffixOf(parent) ==> Length() > parent.Length()
    {
      this != parent && SuffixOf(parent)
    }

    predicate SuffixOf(parent: Name)
      // Check whether `this` descended from `parent`.
      decreases this
      ensures SuffixOf(parent) ==> Length() >= parent.Length()
    {
      || parent == this
      || (this.Name? && this.parent.SuffixOf(parent))
    }

    static lemma {:induction n2} SuffixOf_Transitive(n0: Name, n1: Name, n2: Name)
      requires n2.SuffixOf(n1) && n1.SuffixOf(n0)
      ensures n2.SuffixOf(n0)
    {}

    static lemma {:induction false} StrictSuffixOf_Left_Transitive(n0: Name, n1: Name, n2: Name)
      requires n2.StrictSuffixOf(n1) && n1.SuffixOf(n0)
      ensures n2.StrictSuffixOf(n0)
    {
      SuffixOf_Transitive(n0, n1, n2);
    }

    static lemma {:induction false} StrictSuffixOf_Right_Transitive(n0: Name, n1: Name, n2: Name)
      requires n2.SuffixOf(n1) && n1.StrictSuffixOf(n0)
      ensures n2.StrictSuffixOf(n0)
    {
      SuffixOf_Transitive(n0, n1, n2);
    }
  }
}

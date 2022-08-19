include "../Utils/Library.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Names {
  import Utils.Lib.Set
  import C = Utils.Lib.Sort.Comparison
  import SeqCmp = Utils.Lib.Seq.Comparison
  import StrCmp = Utils.Lib.Str.Comparison
  import DerivedCmp = Utils.Lib.Sort.DerivedComparison

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

    function ToSeq(): seq<Atom> {
      match this
        case Anonymous => []
        case Name(parent, suffix) => parent.ToSeq() + [suffix]
    }

    static lemma {:induction false} ToSeqInj1(n0: Name, n1: Name)
      requires n0.ToSeq() == n1.ToSeq()
      decreases n0.Length()
      ensures n0 == n1
    {
      var s0, s1 := n0.ToSeq(), n1.ToSeq();
      if s0 != [] && s1 != [] {
        assert s0 == s0[..|s0| - 1] + [s0[|s0| - 1]];
        assert s1 == s1[..|s1| - 1] + [s1[|s1| - 1]];
        assert n0.Name? && n1.Name?;
        assert n1.suffix == s1[|s1| - 1] == s0[|s0| - 1] == n0.suffix;
        assert n0.parent.ToSeq() == s0[..|s0| - 1] == s1[..|s1| - 1] == n1.parent.ToSeq();
        ToSeqInj1(n0.parent, n1.parent);
      }
    }

    static lemma ToSeqInj()
      ensures forall n0: Name, n1: Name | n0.ToSeq() == n1.ToSeq() :: n0 == n1
    {
      forall n0: Name, n1: Name | n0.ToSeq() == n1.ToSeq() {
        ToSeqInj1(n0, n1);
      }
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

    static const toSeq: Name -> seq<string> := (name: Name) => name.ToSeq();
    static const AtomSeqComparison := SeqCmp.SeqComparison(StrCmp.Comparison);
    static const NameComparison := DerivedCmp.DerivedComparison(AtomSeqComparison.Comparison, toSeq);
    static const Comparison := NameComparison.Comparison;

    static lemma {:induction false} Total(names: set<Name>)
      ensures Comparison.Total?(names)
    {
      ToSeqInj();
      StrCmp.Total(SeqCmp.Flatten(Set.Map(names, toSeq)));
      AtomSeqComparison.Total(Set.Map(names, toSeq));
      NameComparison.Total(names);
    }
  }
}

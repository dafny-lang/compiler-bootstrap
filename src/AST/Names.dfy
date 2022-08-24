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

    predicate ParentOf(child: Name)
      // Check whether `this` is a direct parent of `child`.
      ensures ParentOf(child) ==> Length() + 1 == child.Length()
    {
      child.ChildOf(this)
    }

    predicate StrictPrefixOf(child: Name)
      // Check whether `this` is an indirect parent of `child`.
      ensures StrictPrefixOf(child) ==> Length() < child.Length()
    {
      this != child && PrefixOf(child)
    }

    predicate PrefixOf(child: Name)
      // Check whether `this` is a direct or indirect parent of `child`.
      ensures PrefixOf(child) ==> Length() <= child.Length()
    {
      || child == this
      || (child.Name? && PrefixOf(child.parent))
    }

    static lemma {:induction n2} PrefixOf_Transitive(n0: Name, n1: Name, n2: Name)
      requires n0.PrefixOf(n1) && n1.PrefixOf(n2)
      ensures n0.PrefixOf(n2)
    {}

    static lemma {:induction false} StrictPrefixOf_Left_Transitive(n0: Name, n1: Name, n2: Name)
      requires n0.StrictPrefixOf(n1) && n1.PrefixOf(n2)
      ensures n0.StrictPrefixOf(n2)
    {
      PrefixOf_Transitive(n0, n1, n2);
    }

    static lemma {:induction false} StrictPrefixOf_Right_Transitive(n0: Name, n1: Name, n2: Name)
      requires n0.PrefixOf(n1) && n1.StrictPrefixOf(n2)
      ensures n0.StrictPrefixOf(n2)
    {
      PrefixOf_Transitive(n0, n1, n2);
    }

    predicate StrictExtensionOf(parent: Name)
      // Check whether one of the parents of `this` is `parent`.
      ensures StrictExtensionOf(parent) ==> Length() > parent.Length()
    {
      parent.StrictPrefixOf(this)
    }

    predicate ExtensionOf(parent: Name)
      // Check whether `this` is descended from `parent`.
      decreases this
      ensures ExtensionOf(parent) ==> Length() >= parent.Length()
    {
      parent.PrefixOf(this)
    }

    static lemma {:induction n2} ExtensionOf_Transitive(n0: Name, n1: Name, n2: Name)
      requires n2.ExtensionOf(n1) && n1.ExtensionOf(n0)
      ensures n2.ExtensionOf(n0)
    {}

    static lemma {:induction false} StrictExtensionOf_Left_Transitive(n0: Name, n1: Name, n2: Name)
      requires n2.StrictExtensionOf(n1) && n1.ExtensionOf(n0)
      ensures n2.StrictExtensionOf(n0)
    {
      ExtensionOf_Transitive(n0, n1, n2);
    }

    static lemma {:induction false} StrictExtensionOf_Right_Transitive(n0: Name, n1: Name, n2: Name)
      requires n2.ExtensionOf(n1) && n1.StrictExtensionOf(n0)
      ensures n2.StrictExtensionOf(n0)
    {
      ExtensionOf_Transitive(n0, n1, n2);
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

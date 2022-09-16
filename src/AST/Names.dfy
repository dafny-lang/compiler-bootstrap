include "../Utils/Library.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Names {
  import Utils.Lib.Seq
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

    function ToDafnyName(): string {
      var parts := Seq.Filter(this.ToSeq(), a => a !in {"_default", "_module"});
      Seq.Flatten(Seq.Interleave(".", parts))
    }

    function Any(P: Atom -> bool): bool {
      match this {
        case Anonymous => false
        case Name(parent, suffix) =>
          P(suffix) || parent.Any(P)
      }
    }

    function IsInternal(): bool {
      Any(suffix => || "reveal_" <= suffix
                    || "_System" == suffix)
    }

    function IsCompile(): bool {
      Any(suffix =>
        // TODO: this is a suffix, so we can't use <=.
        // Is there a better way?
        var parts := Seq.Split('_', suffix);
        parts[|parts| - 1] == "Compile")
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
      || ParentOf(child)
      || (child.Name? && StrictPrefixOf(child.parent))
    }

    predicate PrefixOf(child: Name)
      // Check whether `this` is a direct or indirect parent of `child`.
      ensures PrefixOf(child) ==> Length() <= child.Length()
    {
      || child == this
      || StrictPrefixOf(child)
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

    function NthParent(n: nat): (nth_parent: Name)
      requires n <= Length()
      ensures ExtensionOf(nth_parent)
      ensures nth_parent.Length() == Length() - n
    {
      if n == 0 then this
      else this.parent.NthParent(n - 1)
    }

    lemma NthParent_Extension(ancestor: Name, n: nat)
      requires ExtensionOf(ancestor)
      requires n <= Length() - ancestor.Length()
      ensures NthParent(n).ExtensionOf(ancestor)
    {}

    function TruncateTo(length: nat): (truncated: Name)
      requires length <= Length()
      ensures ExtensionOf(truncated)
      ensures truncated.Length() == length
    {
      NthParent(Length() - length)
    }

    lemma TruncateTo_Extension(ancestor: Name, length: nat)
      requires ExtensionOf(ancestor)
      requires ancestor.Length() <= length <= Length()
      ensures TruncateTo(length).ExtensionOf(ancestor)
    {
      NthParent_Extension(ancestor, Length() - length);
    }

    lemma Length_ChildOf(parent: Name)
      requires Length() == parent.Length() + 1
      requires ExtensionOf(parent)
      ensures ChildOf(parent)
    {}

    function ChildOfAncestor(ancestor: Name): (child: Name)
      requires StrictExtensionOf(ancestor)
      ensures ExtensionOf(child)
      ensures child.ChildOf(ancestor)
    {
      var child := TruncateTo(ancestor.Length() + 1);
      TruncateTo_Extension(ancestor, ancestor.Length() + 1);
      child.Length_ChildOf(ancestor);
      child
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

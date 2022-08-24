/// Dafny's modules, types, and members hierarchy
/// =============================================

include "Names.dfy"
include "Syntax.dfy"
include "../Utils/Library.dfy"
include "../Utils/Lib.Sort.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Entities
  // Hierarchies of Dafny entities.
  // See </doc/design/entities.md>.
{
  import opened Names
  import opened Syntax.Exprs
  import opened Utils.Lib.Datatypes
  import Utils.Lib.SetSort
  import OS = Utils.Lib.Outcome.OfSeq

  // DISCUSS: Should this module be parameterized by `TExpr`?

  datatype Module =
    Module()

  datatype ExportSet =
    ExportSet(provided: set<Name>, revealed: set<Name>)

  datatype Import =
    Import(localName: Atom, target: Name)

  datatype SubsetType =
    SubsetType(boundVar: string, pred: Expr, witnessExpr: Option<Expr>)

  datatype TypeAlias =
    TypeAlias(base: Name)
  datatype AbstractType =
    AbstractType()
  datatype TraitType =
    TraitType(parentTypes: seq<Name>)
  datatype ClassType =
    ClassType(parentTypes: seq<Name>)
  datatype DataType =
    DataType()
  datatype NewType =
    NewType()

  datatype Type =
    | SubsetType(st: SubsetType)
    | TypeAlias(ta: TypeAlias)
    | AbstractType(at: AbstractType)
    | TraitType(tt: TraitType)
    | ClassType(ct: ClassType)
    | DataType(dt: DataType)
    | NewType(nt: NewType)

  datatype FieldKind =
    Const | Var
  datatype Field =
    Field(kind: FieldKind, body: Expr)

  datatype Callable =
    | Method(body: Expr)
    | Function(body: Expr)
    | Constructor(body: Expr)

  datatype Definition =
    | Field(fi: Field)
    | Callable(ci: Callable)

  datatype EntityKind =
    | EModule
    | EExportSet
    | EImport
    | EType
    | EDefinition

  type EntityInfo = e: EntityInfo_ | e.Valid?()
    witness EntityInfo_.EMPTY()
  datatype EntityInfo_ =
    EntityInfo(name: Name, nameonly attrs: seq<Attribute>, nameonly members: seq<Name>)
  {
    static function EMPTY(): (ei: EntityInfo_)
      ensures ei.Valid?()
    {
      EntityInfo(Anonymous, attrs := [], members := [])
    }

    ghost predicate Valid?() {
      forall nm <- members :: nm.ChildOf(name)
    }

    static function Mk(name: Name): EntityInfo
      // Construct an `EntityInfo` instance with no attributes and no members.
    {
      EntityInfo(name, attrs := [], members := [])
    }
  }

  datatype Entity =
    | Module(ei: EntityInfo, m: Module)
    | ExportSet(ei: EntityInfo, e: ExportSet)
    | Import(ei: EntityInfo, i: Import)
    | Type(ei: EntityInfo, t: Type)
    | Definition(ei: EntityInfo, d: Definition)
  {
    const kind :=
      match this
        case Module(ei, m) => EModule
        case ExportSet(ei, e) => EExportSet
        case Import(ei, i) => EImport
        case Type(ei, t) => EType
        case Definition(ei, d) => EDefinition
  }

  datatype AttributeName =
    | Axiom
    | Extern
    | UserAttribute(name: string)
  {
    function ToString(): string {
      match this
        case Axiom => "axiom"
        case Extern => "extern"
        case UserAttribute(name) => name
    }
  }

  datatype Attribute =
    Attribute(name: AttributeName, args: seq<Expr>)
  {
    function ToString(): string {
      "{:" + name.ToString() + (if args != [] then " ..." else "") + "}"
    }
  }

  ghost predicate EntityTransformer?(f: Entity -> Entity) {
    forall e ::
      && f(e).kind == e.kind
      && f(e).ei.name == e.ei.name
      && f(e).ei.members == e.ei.members
  }

  type EntityTransformer = f | EntityTransformer?(f) witness e => e

  datatype ValidationError =
    | NameMismatch(name: Name, key: Name)
    | UnboundMember(name: Name, member: Name)
    | UnboundParent(name: Name, parent: Name)

  type Registry = r: Registry_ | r.Valid?()
    witness Registry_.EMPTY()
  datatype Registry_ = Registry(entities: map<Name, Entity>)
    // A collection of Dafny entities, index by name.
    //
    // The entity graph of a Dafny program is a tree: members of a module or
    // class have names that extend that of the parent module.  This fact allows
    // easy recursion, using the functions `TransitiveMembers` and `TransitiveMembersOfMany`
    // below, along with the recursion lemmas `Decreases_TransitiveMembers_Single`,
    // `Decreases_TransitiveMembers_Many`, and `Decreases_TransitiveMembersOfMany`.
  {
    static function EMPTY(): (r: Registry_)
      ensures r.Valid?()
    {
      Registry(map[])
    }

/// Well-formedness
/// ~~~~~~~~~~~~~~~

    predicate ValidName??(name: Name, entity: Entity) {
      entity.ei.name == name
    }

    predicate ValidParent??(name: Name) {
      || name == Anonymous
      || (name.parent in entities && MemberOf(name, name.parent))
    }

    predicate MemberOf(name: Name, parent: Name)
      requires name.Name?
      requires Contains(name.parent)
    {
      name in entities[name.parent].ei.members
    }

    predicate ValidMembers??(ei: EntityInfo) {
      forall m <- ei.members :: m in entities
    }

    ghost predicate ValidEntry??(name: Name, entity: Entity) {
      && ValidName??(name, entity)
      && ValidParent??(name)
      && ValidMembers??(entity.ei)
    }

    ghost predicate Valid?() {
      forall name <- entities :: ValidEntry??(name, entities[name])
    }

/// Post-construction validation
/// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    function {:opaque} ValidateEntry(name: Name, entity: Entity): (o: Outcome<seq<ValidationError>>)
      requires Lookup(name) == Some(entity)
      ensures o.Pass? <==> ValidEntry??(name, entity)
    {
      assume false; // TODO
      OS.Combine(
        [if ValidName??(name, entity) then Pass else Fail(NameMismatch(name, entity.ei.name)),
         if ValidParent??(name) then Pass else Fail(UnboundParent(name, name.parent))]
        + Seq.Map(m =>
            if m in entities then Pass else Fail(UnboundMember(name, m)),
            entity.ei.members)
      )
    }

    function {:opaque} Validate(): (os: Outcome<seq<ValidationError>>)
      ensures os.Pass? <==> Valid?()
    {
      var names := SortedNames();
      var validate := nm requires Contains(nm) => ValidateEntry(nm, entities[nm]);
      var os := OS.CombineSeq(Seq.Map(validate, names));
      calc <==> {
        os.Pass?;
        forall o <- Seq.Map(validate, names) :: o.Pass?;
        { Seq.Map_in(validate, names); }
        forall name <- names :: validate(name).Pass?;
        forall name <- Set.OfSeq(names) :: ValidEntry??(name, entities[name]);
        { reveal AllNames(); }
        Valid?();
      }
      os
    }

/// Core API
/// ~~~~~~~~

    predicate Contains(name: Name) {
      name in entities
    }

    lemma {:induction false} NthParent_Contains(name: Name, n: nat)
      requires Valid?()
      requires Contains(name)
      requires n <= name.Length()
      ensures Contains(name.NthParent(n))
    {
      if n > 0 {
        NthParent_Contains(name.parent, n - 1);
      }
    }

    lemma {:induction false} TruncateTo_Contains(name: Name, length: nat)
      requires Valid?()
      requires Contains(name)
      requires length <= name.Length()
      ensures Contains(name.TruncateTo(length))
    {
      NthParent_Contains(name, name.Length() - length);
    }

    function Get(name: Name): Entity
      requires Contains(name)
    {
      entities[name]
    }

    function Lookup(name: Name): Option<Entity> {
      if Contains(name) then Some(Get(name)) else None
    }

    predicate HasKind(name: Name, kind: EntityKind) {
      Contains(name) && Get(name).kind == kind
    }

    function Members(name: Name): seq<Name>
      requires Contains(name)
    {
      Get(name).ei.members
    }

    function Add(name: Name, entity: Entity): Registry
      requires Valid?()
      requires !Contains(name)
      requires entity.Module?
      requires ValidEntry??(name, entity) // TODO: Only allows adding "Anonymous"
    {
      this.(entities := entities[name := entity])
    }

    function Map(f: EntityTransformer): Registry requires Valid?() {
      Registry(map name | name in entities :: f(entities[name]))
    }

    function {:opaque} AllNames(): set<Name>
      ensures forall name :: name in AllNames() <==> Contains(name)
    {
      entities.Keys
    }

    function {:opaque} SortedNames(): (all_names: seq<Name>)
      ensures (set name <- all_names) == entities.Keys
    {
      SetSort.Sort(entities.Keys, Name.Comparison)
    }

/// Unordered traversals
/// ~~~~~~~~~~~~~~~~~~~~

    function {:opaque} TransitiveMembers(prefix: Name): set<Name> {
      set name <- entities | name.ExtensionOf(prefix)
    }

    function {:opaque} TransitiveMembersOfMany(prefixes: seq<Name>): set<Name> {
      set prefix <- prefixes, name <- TransitiveMembers(prefix) :: name
    }

    lemma {:induction false} TransitiveMembersOfMany_Le(root: Name, members: seq<Name>)
      requires forall member <- members :: member.ChildOf(root)
      ensures TransitiveMembersOfMany(members) <= TransitiveMembers(root);
    {
      reveal TransitiveMembers();
      reveal TransitiveMembersOfMany();

      forall name <- TransitiveMembersOfMany(members)
        ensures name in TransitiveMembers(root)
      {
        var prefix: Name :| prefix in members && name in TransitiveMembers(prefix);
        Name.ExtensionOf_Transitive(root, prefix, name);
      }
    }

    lemma {:induction false} TransitiveMembersOfMany_Lt(root: Name, members: seq<Name>)
      requires Contains(root)
      requires forall member <- members :: member.ChildOf(root)
      ensures TransitiveMembersOfMany(members) < TransitiveMembers(root);
    {
      reveal TransitiveMembers();
      reveal TransitiveMembersOfMany();

      TransitiveMembersOfMany_Le(root, members);

      assert root in TransitiveMembers(root);
      assert root !in TransitiveMembersOfMany(members);
    }

    lemma {:induction false} TransitiveMembers_Le_Many(names: seq<Name>, name: Name)
      requires name in names
      ensures TransitiveMembers(name) <= TransitiveMembersOfMany(names);
    {
      reveal TransitiveMembers();
      reveal TransitiveMembersOfMany();
    }

    lemma {:induction false} TransitiveMembers_Le(root: Name, member: Name)
      requires member.ChildOf(root)
      ensures TransitiveMembers(member) <= TransitiveMembers(root);
    {
      TransitiveMembersOfMany_Le(root, [member]);
      TransitiveMembers_Le_Many([member], member);
    }

    lemma {:induction false} TransitiveMembers_Lt(root: Name, member: Name)
      requires Contains(root)
      requires member.ChildOf(root)
      ensures TransitiveMembers(member) < TransitiveMembers(root);
    {
      TransitiveMembersOfMany_Lt(root, [member]);
      TransitiveMembers_Le_Many([member], member);
    }

    lemma {:induction false} TransitiveMembers_Extension_Le(root: Name, name: Name)
      requires name.ExtensionOf(root)
      ensures TransitiveMembers(name) <= TransitiveMembers(root)
    {
      if name != root {
        TransitiveMembers_Le(name.parent, name);
        TransitiveMembers_Extension_Le(root, name.parent);
      }
    }

    lemma {:induction false} Decreases_TransitiveMembers_Many(names: seq<Name>, name: Name)
      requires name in names
      ensures TransitiveMembers(name) <= TransitiveMembersOfMany(names);
    {
      TransitiveMembers_Le_Many(names, name);
    }

    lemma {:induction false} Decreases_TransitiveMembers_Single(ei: EntityInfo, member: Name)
      requires Contains(ei.name)
      requires member in ei.members
      ensures TransitiveMembers(member) < TransitiveMembers(ei.name);
    {
     TransitiveMembers_Lt(ei.name, member);
    }

    lemma {:induction false} Decreases_TransitiveMembersOfMany(ei: EntityInfo)
      requires Contains(ei.name)
      ensures TransitiveMembersOfMany(ei.members) < TransitiveMembers(ei.name);
    {
      TransitiveMembersOfMany_Lt(ei.name, ei.members);
    }


    function {:opaque} StrictTransitiveMembers(root: Name): (descendants: set<Name>) {
      set name <- entities | name.StrictExtensionOf(root)
    }

    lemma {:induction false} TransitiveMembers_StrictTransitiveMembers(root: Name)
      requires Contains(root)
      ensures TransitiveMembers(root) == {root} + StrictTransitiveMembers(root)
    {
      reveal TransitiveMembers();
      reveal StrictTransitiveMembers();
    }

    ghost function StrictTransitiveMembers_Partitioned(root: Name): set<Name>
      requires Contains(root)
    {
      set member <- Members(root), name <- TransitiveMembers(member) :: name
    }

    lemma {:induction false} StrictTransitiveMembers_Partition(root: Name)
      requires Valid?()
      requires Contains(root)
      ensures StrictTransitiveMembers(root) == StrictTransitiveMembers_Partitioned(root)
    {
      reveal TransitiveMembers();
      reveal StrictTransitiveMembers();

      var members := Members(root);

      forall name <- StrictTransitiveMembers(root)
        ensures name in StrictTransitiveMembers_Partitioned(root)
      {
        var member := name.ChildOfAncestor(root);
        assert Contains(member) by { TruncateTo_Contains(name, root.Length() + 1); }
        assert member in members;
        assert name in TransitiveMembers(member);
        assert name in StrictTransitiveMembers_Partitioned(root);
      }

      forall name <- StrictTransitiveMembers_Partitioned(root)
        ensures name in StrictTransitiveMembers(root)
      {
        var member :| member in members && name in TransitiveMembers(member);
        Name.StrictExtensionOf_Right_Transitive(root, member, name);
        assert name in StrictTransitiveMembers(root);
      }
    }

/// Depth-first traversal
/// ~~~~~~~~~~~~~~~~~~~~~

    function RecursiveTransitiveMembers(root: Name): (members: seq<Name>)
      requires Valid?()
      requires Contains(root)
      decreases TransitiveMembers(root), 1
    {
      // DISCUSS: We need to name the lambda to prove anything about it below
      [root] + Seq.Flatten(Seq.Map(RecursiveTransitiveMembers'(root), Members(root)))
    }

    function RecursiveTransitiveMembers'(ghost root: Name)
      : (Name --> seq<Name>)
      requires Valid?()
      requires Contains(root)
      decreases TransitiveMembers(root), 0
    {
      member requires member in Members(root) =>
        TransitiveMembers_Lt(root, member);
        RecursiveTransitiveMembers(member)
    }

    lemma {:induction false} RecursiveTransitiveMembers_Le(root: Name, name: Name)
      requires Valid?()
      requires Contains(root)
      decreases TransitiveMembers(root)
      requires name in RecursiveTransitiveMembers(root)
      ensures name in TransitiveMembers(root)
    {
      reveal TransitiveMembers();
      if name != root {
        assert name in Seq.Flatten(Seq.Map(RecursiveTransitiveMembers'(root), Members(root)));
        var member :| member in Members(root) && name in RecursiveTransitiveMembers(member);
        TransitiveMembers_Lt(root, member);
        RecursiveTransitiveMembers_Le(member, name);
        TransitiveMembers_Extension_Le(root, member);
      }
    }

    lemma {:induction false} RecursiveTransitiveMembers_Ge(root: Name, name: Name)
      requires Valid?()
      requires Contains(root)
      decreases TransitiveMembers(root)
      requires name in TransitiveMembers(root)
      ensures name in RecursiveTransitiveMembers(root)
    {
      reveal TransitiveMembers();
      if name != root {
        assert name in StrictTransitiveMembers(root) by {
          TransitiveMembers_StrictTransitiveMembers(root);
        }
        StrictTransitiveMembers_Partition(root);
        assert name in StrictTransitiveMembers_Partitioned(root);
        var member :| member in Members(root) && name in TransitiveMembers(member);
        TransitiveMembers_Lt(root, member);
        RecursiveTransitiveMembers_Ge(member, name);
      }
    }

    lemma {:induction false} RecursiveTransitiveMembers_Eq(root: Name)
      requires Valid?()
      requires Contains(root)
      ensures Set.OfSeq(RecursiveTransitiveMembers(root)) == TransitiveMembers(root)
    {
      forall name ensures name in Set.OfSeq(RecursiveTransitiveMembers(root))
                      <==> name in TransitiveMembers(root)
      {
        if name in Set.OfSeq(RecursiveTransitiveMembers(root)) {
          RecursiveTransitiveMembers_Le(root, name);
        }
        if name in TransitiveMembers(root) {
          RecursiveTransitiveMembers_Ge(root, name);
        }
      }
    }

    lemma {:induction false} RecursiveTransitiveMembers_Extension(root: Name)
      requires Valid?()
      requires Contains(root)
      ensures forall d <- RecursiveTransitiveMembers(root) :: d.ExtensionOf(root)
    {
      forall d <- RecursiveTransitiveMembers(root)
        ensures d.ExtensionOf(root)
      {
        RecursiveTransitiveMembers_Eq(root);
        assert d in TransitiveMembers(root);
        reveal TransitiveMembers();
      }
    }

  }

  type Program = p: Program_ | p.Valid?() witness Program.EMPTY()
  datatype Program_ =
    Program(registry: Registry,
            nameonly defaultModule: Name,
            nameonly mainMethod: Option<Name>)
  {
    static function EMPTY(): (p: Program_) ensures p.Valid?() {
      Program(
        Registry.EMPTY().Add(Anonymous, Entity.Module(EntityInfo.Mk(Anonymous), Module.Module())),
        defaultModule := Anonymous,
        mainMethod := None
      )
    }

    predicate ValidDefaultModule?() {
      registry.HasKind(defaultModule, EModule)
    }

    predicate ValidMainMethod?() {
      mainMethod.Some? ==> registry.HasKind(mainMethod.value, EDefinition) // FIXME
    }

    predicate Valid?() {
      && ValidDefaultModule?()
      && ValidMainMethod?()
    }

    function DefaultModule(): Entity requires Valid?() {
      registry.Get(defaultModule)
    }
  }
}

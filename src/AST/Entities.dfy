/// Dafny's modules, types, and members hierarchy
/// =============================================

include "Names.dfy"
include "Syntax.dfy"
include "../Utils/Library.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Entities
  // Hierarchies of Dafny entities.
  // See </doc/design/entities.md>.
{
  import opened Names
  import opened Syntax.Exprs
  import opened Utils.Lib.Datatypes

  datatype Module =
    Module(members: seq<Name>)

  datatype ExportSet =
    ExportSet(provided: set<Name>, revealed: set<Name>)

  datatype Import =
    Import(localName: Atom, target: Name)

  datatype SubsetType =
    SubsetType(boundVar: string, pred: Expr, witnessExpr: Expr)

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
    | Module(ei: EntityInfo)
    | ExportSet(ei: EntityInfo, e: ExportSet)
    | Import(ei: EntityInfo, i: Import)
    | Type(ei: EntityInfo, t: Type)
    | Definition(ei: EntityInfo, d: Definition)
  {
    const kind :=
      match this
        case Module(ei) => EModule
        case ExportSet(ei, e) => EExportSet
        case Import(ei, i) => EImport
        case Type(ei, t) => EType
        case Definition(ei, d) => EDefinition
  }

  datatype Attribute = // TODO: Move all exprs to top level?
    Attribute(name: string, args: seq<Expr>)
  {
    function ToString(): string {
      "{:" + name + (if args != [] then " ..." else "") + "}"
    }
  }

  ghost predicate EntityMap?(f: Entity -> Entity) {
    forall e ::
      && f(e).kind == e.kind
      && f(e).ei.name == e.ei.name
      && f(e).ei.members == e.ei.members
  }

  type EntityMap = f | EntityMap?(f) witness e => e

  type Registry = r: Registry_ | r.Valid?()
    witness Registry_.EMPTY()
  datatype Registry_ = Registry(entities: map<Name, Entity>)
    // A collection of Dafny entities, index by name.
    //
    // The entity graph of a Dafny program is a tree: members of a module or
    // class have names that extend that of the parent module.  This fact allows
    // easy recursion, using the functions `SuffixesOf` and `SuffixesOfMany`
    // below, along with the two recursion lemmas `Decreases_SuffixesOf` and
    // `Decreases_SuffixesOfMany`.
  {
    static function EMPTY(): (r: Registry_)
      ensures r.Valid?()
    {
      Registry(map[])
    }

    ghost predicate ValidName??(name: Name, entity: Entity) {
      entity.ei.name == name
    }

    ghost predicate ValidParent??(name: Name) {
      name == Anonymous || name.parent in entities
    }

    ghost predicate ValidMembers??(ei: EntityInfo) {
      forall m <- ei.members :: m in entities
    }

    ghost predicate ValidEntry??(name: Name, e: Entity) {
      && ValidName??(name, e)
      && ValidParent??(name)
      && ValidMembers??(e.ei)
    }

    ghost predicate ValidNames?() {
      forall name <- entities :: ValidName??(name, entities[name])
    }

    ghost predicate ValidParents?() {
      forall name <- entities :: ValidParent??(name)
    }

    ghost predicate ValidMembers?() {
      forall name <- entities :: ValidMembers??(entities[name].ei)
    }

    ghost predicate Valid?() {
      forall name <- entities :: ValidEntry??(name, entities[name])
    }

    ghost function {:opaque} SuffixesOf(prefix: Name): set<Name> {
      set name <- entities | name.SuffixOf(prefix)
    }

    ghost function {:opaque} SuffixesOfMany(prefixes: seq<Name>): set<Name> {
      set prefix <- prefixes, name <- SuffixesOf(prefix) :: name
    }

    lemma Decreases_SuffixesOfMany(ei: EntityInfo)
      requires ei.name in entities
      ensures SuffixesOfMany(ei.members) < SuffixesOf(ei.name);
    {
      reveal SuffixesOf();
      reveal SuffixesOfMany();

      assert SuffixesOfMany(ei.members) <= SuffixesOf(ei.name) by {
        forall name <- SuffixesOfMany(ei.members)
          ensures name in SuffixesOf(ei.name)
        {
          var prefix: Name :| prefix in ei.members && name in SuffixesOf(prefix);
          Name.SuffixOf_Transitive(ei.name, prefix, name);
        }
      }

      assert ei.name in SuffixesOf(ei.name);
      assert ei.name !in SuffixesOfMany(ei.members);
    }

    lemma {:induction false} Decreases_SuffixesOf(names: seq<Name>, name: Name)
      requires name in names
      ensures SuffixesOf(name) <= SuffixesOfMany(names);
    {
      reveal SuffixesOf();
      reveal SuffixesOfMany();
    }

    predicate Contains(name: Name) {
      name in entities
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

    function Add(name: Name, entity: Entity): Registry
      requires Valid?()
      requires !Contains(name)
      requires entity.Module?
      requires ValidEntry??(name, entity)
    {
      this.(entities := entities[name := entity])
    }

    function Map(f: EntityMap): Registry
      requires Valid?()
    {
      Registry(map name | name in entities :: f(entities[name]))
    }
  }

  type Program = p: Program_ | p.Valid?() witness Program.EMPTY()
  datatype Program_ =
    Program(r: Registry,
            defaultModule: Name,
            mainMethod: Option<Name>)
  {
    static function EMPTY(): (p: Program_) ensures p.Valid?() {
      Program(
        Registry.EMPTY().Add(Anonymous, Entity.Module(EntityInfo.Mk(Anonymous))),
        defaultModule := Anonymous,
        mainMethod := None
      )
    }

    predicate ValidDefaultModule?() {
      r.HasKind(defaultModule, EModule)
    }

    predicate ValidMainMethod?() {
      mainMethod.Some? ==> r.HasKind(mainMethod.value, EModule)
    }

    predicate Valid?() {
      && ValidDefaultModule?()
      && ValidMainMethod?()
    }
  }
}

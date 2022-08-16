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
    witness EntityInfo(Anonymous, attrs := [], members := [])
  datatype EntityInfo_ =
    EntityInfo(name: Name, nameonly attrs: seq<Attribute>, nameonly members: seq<Name>)
  {
    ghost predicate Valid?() {
      forall nm <- members :: nm.ChildOf(name)
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
    witness Registry(map[])
  datatype Registry_ = Registry(entities: map<Name, Entity>)
    // A collection of Dafny entities, index by name.
    //
    // The entity graph of a Dafny program is a tree: members of a module or
    // class have names that extend that of the parent module.  This fact allows
    // easy recursion, using the functions `SuffixesOf` and `SuffixesOfMany`
    // below, along with the two recursion lemmas `Decreases_SuffixesOf` and
    // `Decreases_SuffixesOfMany`.
  {
    ghost predicate ValidNames?() {
      forall n <- entities :: entities[n].ei.name == n
    }

    ghost predicate ValidParent??(n: Name) {
      n == Anonymous || n.parent in entities
    }

    ghost predicate ValidParents?() {
      forall n <- entities :: ValidParent??(n)
    }

    ghost predicate ValidMembers??(ei: EntityInfo) {
      forall m <- ei.members :: m in entities
    }

    ghost predicate ValidMembers?() {
      forall n <- entities :: ValidMembers??(entities[n].ei)
    }

    ghost predicate Valid?() {
      && ValidNames?()
      && ValidParents?()
      && ValidMembers?()
    }

    ghost function {:opaque} SuffixesOf(name: Name): set<Name> {
      set n <- entities | n.SuffixOf(name)
    }

    ghost function {:opaque} SuffixesOfMany(names: seq<Name>): set<Name> {
      set n <- names, sf <- SuffixesOf(n) :: sf
    }

    lemma Decreases_SuffixesOfMany(ei: EntityInfo)
      requires ei.name in entities
      ensures SuffixesOfMany(ei.members) < SuffixesOf(ei.name);
    {
      reveal SuffixesOf();
      reveal SuffixesOfMany();

      assert SuffixesOfMany(ei.members) <= SuffixesOf(ei.name) by {
        forall sf <- SuffixesOfMany(ei.members)
          ensures sf in SuffixesOf(ei.name)
        {
          var name: Name :| name in ei.members && sf in SuffixesOf(name);
          Name.SuffixOf_Transitive(ei.name, name, sf);
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

    function Find(n: Name) : Option<Entity> {
      if n in entities then Some(entities[n]) else None
    }

    function Map(f: EntityMap) : Registry
      requires Valid?()
    {
      Registry(map n | n in entities :: f(entities[n]))
    }
  }
}

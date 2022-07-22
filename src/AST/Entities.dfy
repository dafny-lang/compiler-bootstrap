/// Dafny's modules, types, and members hierarchy
/// =============================================

include "Names.dfy"
include "Syntax.dfy"
include "../Utils/Library.dfy"

module Bootstrap.AST.Entities
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

  datatype Field =
    | Field(tp: Type)

  datatype FuncKind =
    Method | Function | Constructor
  datatype Func =
    | Func(kind: FuncKind, body: Expr)

  datatype RawEntity =
    | Module(children: seq<Name>)
    | ExportSet(provided: set<Name>, revealed: set<Name>)
    | Import(localName: Atom, target: Name)
    | Type(children: seq<Name>)
    | Definition()

  datatype Attribute =
    Attribute(name: string, value: Expr)

  datatype Entity =
    Entity(e: RawEntity, attrs: seq<Attribute>, children: seq<Name>)

  datatype NamedEntity =
    NamedEntity(n: Name, e: Entity)

  datatype Registry = Registry(entities: map<Name, Entity>) {
    function method Find(n: Name) : Option<Entity> {
      if n in entities then Some(entities[n]) else None
    }

    function method Map(f: NamedEntity -> Entity) : Registry {
      Registry(map n | n in entities :: f(NamedEntity(n, entities[n])))
    }
  }
}

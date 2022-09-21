include "../AST/Entities.dfy"
include "../AST/Syntax.dfy"
include "../AST/Predicates.dfy"
include "Generic.dfy"

module Bootstrap.Transforms.Shallow {
  import opened Utils.Lib
  import opened Utils.Lib.Datatypes
  import opened AST.Entities
  import opened AST.Syntax
  import opened AST.Predicates
  import opened Generic

  function method {:opaque} Map_Module(ent: Module, tr: ExprTransformer) : (ent': Module)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e)
  {
    Module.Module()
  }

  function method {:opaque} Map_ExportSet(ent: ExportSet, tr: ExprTransformer) : (ent': ExportSet)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e)
  {
    ExportSet.ExportSet(provided := ent.provided, revealed := ent.revealed)
  }

  function method {:opaque} Map_Import(ent: Import, tr: ExprTransformer) : (ent': Import)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e)
  {
    Import.Import(localName := ent.localName, target := ent.target)
  }

  function method {:opaque} Map_SubsetType(ent: SubsetType, tr: ExprTransformer) : (ent': SubsetType)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e)
  {
    SubsetType.SubsetType(
      boundVar := ent.boundVar, ty := ent.ty, pred := tr.f(ent.pred),
      witnessExpr := ent.witnessExpr.Map(tr.f), isNewType := ent.isNewType
    )
  }

  function method {:opaque} Map_Type(ent: Entities.Type, tr: ExprTransformer) : (ent': Entities.Type)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e)
  {
    match ent
      case SubsetType(st) => Entities.Type.SubsetType(Map_SubsetType(st, tr))
      case TypeAlias(ta) => Entities.Type.TypeAlias(ta)
      case AbstractType(at) => Entities.Type.AbstractType(at)
      case TraitType(tt) => Entities.Type.TraitType(tt)
      case ClassType(ct) => Entities.Type.ClassType(ct)
      case DataType(dt) => Entities.Type.DataType(dt)
      case Unsupported(desc) => Entities.Type.Unsupported(desc)
  }

  function method {:opaque} Map_Field(ent: Field, tr: ExprTransformer) : (ent': Field)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e) // FIXME Deep
  {
    Field.Field(kind := ent.kind, body := ent.body.Map(tr.f))
  }

  function method {:opaque} Map_Callable(ent: Callable, tr: ExprTransformer) : (ent': Callable)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e) // FIXME Deep
  {
    var req' := Seq.Map(tr.f, ent.req);
    var ens' := Seq.Map(tr.f, ent.ens);
    var body' := ent.body.Map(tr.f);
    match ent {
      case Constructor(_, _, _) => Constructor(req', ens', body')
      case Function(_, _, _) => Function(req', ens', body')
      case Method(_, _, _) => Method(req', ens', body')
    }
  }

  function method {:opaque} Map_Definition(ent: Definition, tr: ExprTransformer) : (ent': Definition)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e)
  {
    match ent
      case Field(fi) => Definition.Field(Map_Field(fi, tr))
      case Callable(ci) => Definition.Callable(Map_Callable(ci, tr))
  }

  function method {:opaque} Map_Attribute(ent: Attribute, tr: ExprTransformer) : (ent': Attribute)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e)
  {
    Attribute(name := ent.name, args := Seq.Map(tr.f, ent.args))
  }

  function method {:opaque} Map_EntityInfo(ent: EntityInfo, tr: ExprTransformer) : (ent': EntityInfo)
    requires forall e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall e <- ent'.Exprs() :: tr.post(e)
    ensures ent'.name == ent.name
    ensures ent'.members == ent.members
  {
    assert forall nm <- ent.members :: nm.ChildOf(ent.name); // BUG: `Valid?`, needed by IDE
    assert forall a <- ent.attrs, e <- a.Exprs() :: e in ent.Exprs();
    var ei': EntityInfo := EntityInfo(name := ent.name, location := ent.location,
      attrs := Seq.Map(a requires a in ent.attrs => Map_Attribute(a, tr), ent.attrs),
      members := ent.members);
    ei'
  }

  function method {:opaque} Map_Entity(e: Entity, tr: ExprTransformer) : (e': Entity)
    requires Shallow.All_Entity(e, tr.f.requires)
    ensures Shallow.All_Entity(e', tr.post)
    ensures e'.kind == e.kind
    ensures e'.ei.name == e.ei.name
    ensures e'.ei.members == e.ei.members
  {
    match e {
      case Module(ei, m) => Entity.Module(Map_EntityInfo(ei, tr), Map_Module(m, tr))
      case ExportSet(ei, e) => Entity.ExportSet(Map_EntityInfo(ei, tr), Map_ExportSet(e, tr))
      case Import(ei, i) => Entity.Import(Map_EntityInfo(ei, tr), Map_Import(i, tr))
      case Type(ei, t) => Entity.Type(Map_EntityInfo(ei, tr), Map_Type(t, tr))
      case Definition(ei, d) => Entity.Definition(Map_EntityInfo(ei, tr), Map_Definition(d, tr))
      case Unsupported(ei, desc) => Entity.Unsupported(Map_EntityInfo(ei, tr), desc)
    }
  }

  function method Map_EntityTransformer(tr: ExprTransformer): (Entity --> Entity) {
    e requires Shallow.All_Entity(e, tr.f.requires) => Map_Entity(e, tr)
  }

  // TODO: prove!
  lemma Map_EntityIsEntityTransformer(tr: ExprTransformer)
    ensures EntityTransformer?(Map_EntityTransformer(tr))
  {
    assume EntityTransformer?(Map_EntityTransformer(tr));
  }

  function method {:opaque} Map_Registry(r: Registry, tr: ExprTransformer) : (r': Registry)
    requires forall ent <- r.entities.Values, e <- ent.Exprs() :: tr.f.requires(e)
    ensures forall ent <- r'.entities.Values, e <- ent.Exprs() :: tr.post(e)
    ensures r'.MappedFrom?(r)
  {
    Map_EntityIsEntityTransformer(tr);
    r.Map(Map_EntityTransformer(tr))
  }

  function method {:opaque} Map_Program(p: Program, tr: ExprTransformer) : (p': Program)
    requires Shallow.All_Program(p, tr.f.requires)
    ensures Shallow.All_Program(p', tr.post)
  {
    var reg' := Map_Registry(p.registry, tr);
    var p' := Program(reg', defaultModule := p.defaultModule, mainMethod := p.mainMethod);
    calc <== {
      Shallow.All_Program(p', tr.post);
      forall e <- p'.Exprs() :: tr.post(e);
      forall ent <- p'.registry.AllRecursiveTransitiveEntities(), e <- ent.Exprs() :: tr.post(e);
      forall ent <- p'.registry.entities.Values, e <- ent.Exprs() :: tr.post(e);
    }
    p'
  }
}

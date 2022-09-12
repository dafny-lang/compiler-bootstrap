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

  function method {:opaque} Map_Callable(c: Callable, tr: ExprTransformer) : (c': Callable)
    requires Shallow.All_Callable(c, tr.f.requires)
    ensures Shallow.All_Callable(c', tr.post) // FIXME Deep
  {
    var req' := Seq.Map(tr.f, c.req);
    var ens' := Seq.Map(tr.f, c.ens);
    var body' := c.body.Map(tr.f);
    match c {
      case Constructor(_, _, _) => Constructor(req', ens', body')
      case Function(_, _, _) => Function(req', ens', body')
      case Method(_, _, _) => Method(req', ens', body')
    }
  }

  function method {:opaque} Map_Entity(e: Entity, tr: ExprTransformer) : (e': Entity)
    requires Shallow.All_Entity(e, tr.f.requires)
    ensures Shallow.All_Entity(e', tr.post)
    ensures e'.kind == e.kind
    ensures e'.ei.name == e.ei.name
    ensures e'.ei.members == e.ei.members
  {
    match e {
      case Definition(ei, d) =>
        if d.Callable? then
          Definition(ei, Callable(Map_Callable(d.ci, tr)))
        else e
      // TODO: add fields once they contain expressions
      case _ => e
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

  function method {:opaque} Map_Program(p: Program, tr: ExprTransformer) : (p': Program)
    requires Shallow.All_Program(p, tr.f.requires)
    ensures Shallow.All_Program(p', tr.post)
  {
    Map_EntityIsEntityTransformer(tr);
    var reg' := p.registry.Map(Map_EntityTransformer(tr));
    Program(reg', defaultModule := p.defaultModule, mainMethod := p.mainMethod)
  }
}

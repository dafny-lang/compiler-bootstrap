include "../AST/Syntax.dfy"
include "../AST/Predicates.dfy"
include "Generic.dfy"

module Bootstrap.Transforms.Shallow {
  import opened Utils.Lib
  import opened AST.Syntax
  import opened AST.Predicates
  import opened Generic

  function method {:opaque} Map_Method(m: Method, tr: ExprTransformer) : (m': Method)
    requires Shallow.All_Method(m, tr.f.requires)
    ensures Shallow.All_Method(m', tr.post) // FIXME Deep
    ensures tr.rel(m.methodBody, m'.methodBody)
  {
    match m {
      case Method(CompileName, methodBody) =>
        Method (CompileName, tr.f(methodBody))
    }
  }

  function method {:opaque} Map_Program(p: Program, tr: ExprTransformer) : (p': Program)
    requires Shallow.All_Program(p, tr.f.requires)
    ensures Shallow.All_Program(p', tr.post)
    ensures tr.rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
  {
    match p {
      case Program(mainMethod) => Program(Map_Method(mainMethod, tr))
    }
  }
}

include "../AST/Syntax.dfy"
include "../Semantics/Equiv.dfy"

module Bootstrap.Passes.Pass {
    // Abstract module describing a compiler pass.

    import opened AST.Syntax
    import opened Semantics.Equiv

    predicate Tr_Pre(p: Program)
    // The precondition of the transformation

    predicate Tr_Post(p: Program)
    // The postcondition of the transformation

    function method Apply(p: Program) : (p': Program)
    // The transformation itself.
    //
    // For now, we enforce the use of ``EqInterp`` as the binary relation between
    // the input and the output.
      requires Tr_Pre(p)
      ensures Tr_Post(p)
      ensures EqInterp(p.mainMethod.methodBody, p'.mainMethod.methodBody)
}

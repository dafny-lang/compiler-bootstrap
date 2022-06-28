include "Interop/CSharpDafnyASTModel.dfy"
include "Interop/CSharpInterop.dfy"
include "Interop/CSharpDafnyInterop.dfy"
include "Interop/CSharpDafnyASTInterop.dfy"
include "Utils/Library.dfy"
include "Utils/StrTree.dfy"
include "Semantics/Interp.dfy"
include "Semantics/Equiv.dfy"
include "Transforms/Generic.dfy"
include "Transforms/BottomUp.dfy"

module Bootstrap.CompilerRewriter {
  abstract module Pass {
    // Abstract module describing a compiler pass.

    import opened AST.Syntax
    import opened Semantics.Equiv

    // The precondition of the transformation
    predicate Tr_Pre(p: Program)

    // The postcondition of the transformation
    predicate Tr_Post(p: Program)

    // The transformation itself.
    //
    // For now, we enforce the use of ``EqInterp`` as the binary relation between
    // the input and the output.
    function method Apply(p: Program) : (p': Program)
      requires Tr_Pre(p)
      ensures Tr_Post(p)
      ensures EqInterp(p.mainMethod.methodBody, p'.mainMethod.methodBody)
  }
}

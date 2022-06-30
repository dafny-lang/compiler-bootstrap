include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Transforms/BottomUp.dfy"

module Bootstrap.Passes.EliminateNegatedBinops {
  // TODO(SMH): I don't manage to make ``EliminateNegatedBinops`` refine ``Pass``
  // TODO(SMH): the above refactoring might actually hurt, as ``SimplifyEmptyBlocks`` actually
  // reuses some of the proofs of ``EliminateNegatedBinops``.
  // This module implements a simple pass, by which we decompose the "negated" binops
  // into a negation of the "original" binop.
  //
  // Ex.:
  // ====
  // ```
  // x !in set    ~~>   !(x in set)
  // ```

  import Utils.Lib
  import Utils.Lib.Debug
  import opened Utils.Lib.Datatypes
  import opened Transforms.BottomUp

  import opened AST.Syntax
  import opened AST.Predicates
  import opened Semantics.Interp
  import opened Semantics.Values
  import opened Semantics.Equiv
  import opened Transforms.Generic
  import opened Transforms.Proofs.BottomUp_

  type Expr = Syntax.Expr

  function method FlipNegatedBinop_Aux(op: BinaryOps.BinaryOp)
    : (op': BinaryOps.BinaryOp)
    // Auxiliary function (no postcondition) to avoid non-termination.
    // Without this there is a loop between the ``requires`` of
    // FlipNegatedBinop and the body of ``IsNegatedBinop``.
  {
    match op
      case Eq(NeqCommon) => BinaryOps.Eq(BinaryOps.EqCommon)
      case Sequences(SeqNeq) => BinaryOps.Sequences(BinaryOps.SeqEq)
      case Sequences(NotInSeq) => BinaryOps.Sequences(BinaryOps.InSeq)
      case Sets(SetNeq) => BinaryOps.Sets(BinaryOps.SetEq)
      case Sets(NotInSet) => BinaryOps.Sets(BinaryOps.InSet)
      case Multisets(MultisetNeq) => BinaryOps.Multisets(BinaryOps.MultisetEq)
      case Multisets(NotInMultiset) => BinaryOps.Multisets(BinaryOps.InMultiset)
      case Maps(MapNeq) => BinaryOps.Maps(BinaryOps.MapEq)
      case Maps(NotInMap) => BinaryOps.Maps(BinaryOps.InMap)
      case _ => op
  }

  // TODO(SMH): add a "_Single" prefix
  function method FlipNegatedBinop(op: BinaryOps.BinaryOp)
    : (op': BinaryOps.BinaryOp)
    ensures !IsNegatedBinop(op')
  {
    FlipNegatedBinop_Aux(op)
  }

  predicate method IsNegatedBinop(op: BinaryOps.BinaryOp) {
    FlipNegatedBinop_Aux(op) != op
  }

  predicate method IsNegatedBinopExpr(e: Exprs.T) {
    match e {
      case Apply(Eager(BinaryOp(op)), _) => IsNegatedBinop(op)
      case _ => false
    }
  }

  predicate NotANegatedBinopExpr(e: Exprs.T) {
    !IsNegatedBinopExpr(e)
  }

  predicate Tr_Expr_Post(e: Exprs.T) {
    NotANegatedBinopExpr(e)
  }

  predicate Tr_Expr_Rel(e: Exprs.T, e': Exprs.T) {
    EqInterp(e, e')
  }

  function method FlipNegatedBinop_Expr(op: BinaryOp, args: seq<Expr>) : (e':Exprs.T)
    requires IsNegatedBinop(op)
    requires EagerOpSupportsInterp(Exprs.BinaryOp(op))
    ensures (|args| == 2 && (forall i | 0 <= i < |args| :: SupportsInterp(args[i]))) ==> SupportsInterp(e')
  {
    reveal SupportsInterp();
    var si := (|args| == 2 && (forall i | 0 <= i < |args| :: SupportsInterp(args[i])));

    var bop' := Exprs.BinaryOp(FlipNegatedBinop(op));
    var flipped := Exprs.Apply(Exprs.Eager(bop'), args);

    assert si ==> SupportsInterp(flipped);

    var e' := Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [flipped]);

    assert SupportsInterp(flipped) ==> SupportsInterp(e');
    e'
  }

  lemma FlipNegatedBinop_Binop_Rel_Lem(
    e: Interp.Expr, e': Interp.Expr, op: BinaryOp, v0: WV, v1: WV, v0': WV, v1': WV
  )
    requires IsNegatedBinop(op)
    requires EagerOpSupportsInterp(Exprs.BinaryOp(op))
    requires EqValue(v0, v0')
    requires EqValue(v1, v1')
    ensures (
      match (InterpBinaryOp(e, op, v0, v1), InterpBinaryOp(e', FlipNegatedBinop(op), v0', v1'))
        case (Success(b), Success(b')) =>
          && b.Bool?
          && b'.Bool?
          && b.b == ! b'.b
        case (Failure(_), Failure(_)) =>
          true
        case _ =>
          false)
  {
    assume TODO();
    reveal InterpBinaryOp();
    EqValue_HasEqValue_Eq_Lem(v0, v0');
    EqValue_HasEqValue_Eq_Lem(v1, v1');
  }

  lemma FlipNegatedBinop_Expr_Rel_Lem(op: BinaryOp, args: seq<Expr>)
    requires IsNegatedBinop(op)
    ensures (
      var e := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(op)), args);
      var e' := FlipNegatedBinop_Expr(op, args);
      Tr_Expr_Rel(e, e')
    )
  {
    reveal InterpExpr();
    reveal InterpFunctionCall();
    reveal InterpBinaryOp();

    var bop := Exprs.BinaryOp(op);
    var bop' := Exprs.BinaryOp(FlipNegatedBinop(op));
    var e := Exprs.Apply(Exprs.Eager(bop), args);
    var e' := FlipNegatedBinop_Expr(op, args);
    reveal SupportsInterp(); // TODO: remove?

    if SupportsInterp(e) {
      assert SupportsInterp(e');

      // Prove that for every fuel and context, the interpreter returns the same result
      forall env, ctx, ctx' | EqState(ctx, ctx')
        ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx')) {
        var res := InterpExpr(e, env, ctx);
        var res' := InterpExpr(e', env, ctx');

        var args_res := InterpExprs(args, env, ctx);
        var args_res' := InterpExprs(args, env, ctx');
        EqInterp_Seq_Refl_Lem(args);
        InterpExprs_EqInterp_Lem(args, args, env, ctx, ctx');
        assert EqInterpResultSeqValue(args_res, args_res');

        var flipped := Exprs.Apply(Exprs.Eager(bop'), args);
        InterpExprs1_Strong_Lem(flipped, env, ctx');

        if args_res.Success? {
          assert args_res'.Success?;

          var Return(vs, ctx1) := args_res.value;
          var Return(vs', ctx1') := args_res'.value;

          var res1 := InterpBinaryOp(e, op, vs[0], vs[1]);
          var res1' := InterpBinaryOp(e', FlipNegatedBinop(op), vs'[0], vs'[1]);
          FlipNegatedBinop_Binop_Rel_Lem(e, e', op, vs[0], vs[1], vs'[0], vs'[1]);

          assert res1.Success? == res1'.Success?;
          if res1.Success? {
            var b := res1.value;
            var b' := res1'.value;

            assert b.Bool?;
            assert b'.Bool?;
            assert b.b == !b'.b;

            assert EqState(ctx1, ctx1');

            reveal InterpUnaryOp();
          }
          else {
            // Trivial
          }
        }
        else {
          // Trivial
        }
      }
    }
    else {
      assert Tr_Expr_Rel(e, e');
    }
  }

  function method Tr_Expr_Shallow(e: Exprs.T) : (e': Exprs.T)
    ensures Tr_Expr_Post(e')
    ensures Tr_Expr_Rel(e, e')
  {
    EqInterp_Refl_Lem(e);
    match e {
      case Apply(Eager(BinaryOp(op)), args) =>
        if IsNegatedBinop(op) then
          var e' := FlipNegatedBinop_Expr(op, args);
          FlipNegatedBinop_Expr_Rel_Lem(op, args);
          e'
        else
          e
      case _ => e
    }
  }

  lemma TrMatchesPrePost()
    ensures TransformerMatchesPrePost(Tr_Expr_Shallow, Tr_Expr_Post)
  {}

  lemma TrPreservesPre()
    ensures MapChildrenPreservesPre(Tr_Expr_Shallow,Tr_Expr_Post)
  {}

  lemma TransformationAndRel_Lift_Lem(f: Expr --> Expr, rel: (Expr, Expr) -> bool)
    requires RelIsTransitive(rel)
    requires RelCanBeMapLifted(rel)
    requires TransformerShallowPreservesRel(f, rel)
    ensures TransformerDeepPreservesRel(f, rel)
  {}

  lemma TrPreservesRel()
    ensures TransformerDeepPreservesRel(Tr_Expr_Shallow, Tr_Expr_Rel)
  {
    var f := Tr_Expr_Shallow;
    var rel := Tr_Expr_Rel;

    EqInterp_IsTransitive_Lem();
    EqInterp_CanBeMapLifted_Lem();
    TransformationAndRel_Lift_Lem(f, rel);
  }

  const Tr_Expr : BottomUpTransformer :=
    ( TrMatchesPrePost();
      TrPreservesPre();
      TrPreservesRel();
      TR(Tr_Expr_Shallow,
         Tr_Expr_Post,
         Tr_Expr_Rel))


  predicate Tr_Pre(p: Program) {
    true
  }

  predicate Tr_Post(p: Program)
  {
    Deep.All_Program(p, Tr_Expr_Post)
  }

  lemma Tr_Pre_Expr_IsTrue(e: Expr)
    ensures Deep.All_Expr(e, Tr_Expr.f.requires)
    decreases e, 1
  // It is not obvious that `Deep.All_Expr(e, _ => true)` is true...
  // Also, because the functions encoding is not very precise, we can't
  // use the lemma ``Deep.All_Expr_true``.
  {
    Tr_Pre_ChildrenExpr_IsTrue(e);
  }

  lemma Tr_Pre_ChildrenExpr_IsTrue(e: Expr)
    ensures Deep.AllChildren_Expr(e, Tr_Expr.f.requires)
    decreases e, 0
  {
    forall e' | e' in e.Children() { Tr_Pre_Expr_IsTrue(e'); }
  }

  function method Apply_Method(m: Method) : (m': Method)
    ensures Deep.All_Method(m', Tr_Expr_Post)
    ensures Tr_Expr_Rel(m.methodBody, m'.methodBody)
    // Apply the transformation to a method.
    //
    // We need it on a temporary basis, so that we can apply the transformation
    // to all the methods in a program (we haven't defined modules, classes,
    // etc. yet). When the `Program` definition is complete enough, we will
    // remove this definition and exclusively use `Apply`.
  {
    
    Tr_Pre_Expr_IsTrue(m.methodBody);
    assert Deep.All_Method(m, Tr_Expr.f.requires);
    Map_Method(m, Tr_Expr)
  }

  function method Apply(p: Program) : (p': Program)
    requires Tr_Pre(p)
    ensures Tr_Post(p')
    ensures Tr_Expr_Rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
    // Apply the transformation to a program.
  {
    Tr_Pre_Expr_IsTrue(p.mainMethod.methodBody);
    assert Deep.All_Program(p, Tr_Expr.f.requires);
    Map_Program(p, Tr_Expr)
  }
}

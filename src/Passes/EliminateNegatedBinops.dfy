include "../Interop/CSharpDafnyModel.dfy"
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

  import opened AST.Entities
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

  function method FlipNegatedBinop_Single(op: BinaryOp, args: seq<Expr>) : (e':Exprs.T)
    requires IsNegatedBinop(op)
    requires EagerOpSupportsInterp(Exprs.BinaryOp(op))
    ensures (|args| == 2 && (forall i | 0 <= i < |args| :: SupportsInterp(args[i]))) ==> SupportsInterp(e')
    // Flip the negated binary operations of a single expression (don't recurse on its children)
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

  lemma FlipNegatedBinop_Binop_Rel(
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
    reveal InterpBinaryOp();
    EqValue_HasEqValue_Eq(v0, v0');
    EqValue_HasEqValue_Eq(v1, v1');
  }

  lemma FlipNegatedBinop_Single_Rel(op: BinaryOp, args: seq<Expr>)
    requires IsNegatedBinop(op)
    ensures (
      var e := Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(op)), args);
      var e' := FlipNegatedBinop_Single(op, args);
      Tr_Expr_Rel(e, e')
    )
  {
    reveal InterpExpr();
    reveal InterpFunctionCall();
    reveal InterpBinaryOp();

    var bop := Exprs.BinaryOp(op);
    var bop' := Exprs.BinaryOp(FlipNegatedBinop(op));
    var e := Exprs.Apply(Exprs.Eager(bop), args);
    var e' := FlipNegatedBinop_Single(op, args);
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
        EqInterp_Seq_Refl(args);
        InterpExprs_EqInterp_Inst(args, args, env, ctx, ctx');
        assert EqInterpResultSeqValue(args_res, args_res');

        var flipped := Exprs.Apply(Exprs.Eager(bop'), args);
        InterpExprs1_Strong_Eq(flipped, env, ctx');

        if args_res.Success? {
          assert args_res'.Success?;

          var Return(vs, ctx1) := args_res.value;
          var Return(vs', ctx1') := args_res'.value;

          var res1 := InterpBinaryOp(e, op, vs[0], vs[1]);
          var res1' := InterpBinaryOp(e', FlipNegatedBinop(op), vs'[0], vs'[1]);
          FlipNegatedBinop_Binop_Rel(e, e', op, vs[0], vs[1], vs'[0], vs'[1]);

          assert res1.Success? ==> res1'.Success?;
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

  function method Tr_Expr_Single(e: Exprs.T) : (e': Exprs.T)
    ensures Tr_Expr_Post(e')
    ensures Tr_Expr_Rel(e, e')
  {
    EqInterp_Refl(e);
    match e {
      case Apply(Eager(BinaryOp(op)), args) =>
        if IsNegatedBinop(op) then
          var e' := FlipNegatedBinop_Single(op, args);
          FlipNegatedBinop_Single_Rel(op, args);
          e'
        else
          e
      case _ => e
    }
  }

  lemma TrMatchesPrePost()
    ensures TransformerMatchesPrePost(Tr_Expr_Single, Tr_Expr_Post)
  {}

  lemma TrPreservesPre()
    ensures MapChildrenPreservesPre(Tr_Expr_Single,Tr_Expr_Post)
  {}

  lemma TrPreservesRel()
    ensures TransformerDeepPreservesRel(Tr_Expr_Single, Tr_Expr_Rel)
  {
    var f := Tr_Expr_Single;
    var rel := Tr_Expr_Rel;

    EqInterp_Lift(f);
  }

  const Tr_Expr : BottomUpTransformer :=
    ( TrMatchesPrePost();
      TrPreservesPre();
      TR(Tr_Expr_Single,
         Tr_Expr_Post))


  predicate Tr_Pre(p: Program) {
    true
  }

  predicate Tr_Post(p: Program)
  {
    Deep.All_Program(p, Tr_Expr_Post)
  }

  function method Apply(p: Program) : (p': Program)
    requires Tr_Pre(p)
    ensures Tr_Post(p')
    // TODO
    //ensures Tr_Expr_Rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
    // Apply the transformation to a program.
  {
    Deep.All_Expr_True_Forall(Tr_Expr.f.requires);
    assert Deep.All_Program(p, Tr_Expr.f.requires);
    TrPreservesRel();
    // TODO
    //Map_Program_PreservesRel(p, Tr_Expr, Tr_Expr_Rel);
    Map_Program(p, Tr_Expr)
  }
}

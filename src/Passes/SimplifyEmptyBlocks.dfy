include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Semantics/Pure.dfy"
include "../Transforms/BottomUp.dfy"
include "EliminateNegatedBinops.dfy"

module Bootstrap.Passes.SimplifyEmptyBlocks {
  // This module implements a pass that simplifies empty blocks in a program.
  //
  // We do the following:
  //
  // 1. we filter empty blocks in blocks of expressions (``FilterEmptyBlocks``):
  //   ```
  //   var x := f();
  //   g();
  //   {
  //     // empty block
  //   }
  //   h();
  //   ...
  //
  //      --->
  //
  //   var x := f();
  //   g();
  //   h();
  //   ...
  //   ```
  //
  // 2. we inline the blocks that end blocks (note that we can't inline other blocks because of scoping
  //   issues) (``InlineLastBlock``):
  //   ```
  //   var x := f();
  //   {
  //     g();
  //     h();
  //   }
  //
  //      --->
  //
  //   var x := f();
  //   g();
  //   h();
  //   ```
  //
  // 3. We simplify `if then else` expressions when their branches contain empty blocks (``SimplifyIfThenElse``):
  //    ```
  //    if b then {} else {} --> {} // if b is pure
  //    if b then {} else e --> if !b then e else {} // This allows us to only print `if !b then e` in the output program
  //    ```
  //
  // Rk.: those transformations are complementary if performed in a bottom-up manner, as simplifying
  // some blocks might lead to the simplification of some `if then else` branches which might in
  // turn lead to the simplification of other blocks, etc.
  //
  // Rk.: pass 3. removes expressions that might fail. A pass like (3.) is correct because, following definition of ``EqInterp``, the original program (before simplification) is assumed to not fail. 
  //
  // Rk.: one reason why we need these passes is that Dafny-in-Dafny unifies let
  // expressions and variable-declaration statements. For let expressions, this
  // can lead to the introduction of unnecessary blocks and hurt readability.
  //   ```
  //   var x := 3; // let-binding expression
  //   var y := true; // let-binding expression
  //   ...
  //
  //     --->
  //
  //   {
  //     var x := 3; // var decl statement
  //     {
  //       var y := true; // var decl statement
  //       ...
  //     }
  //   }
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

  module FilterCommon {
    import Utils.Lib
    import Utils.Lib.Debug

    import opened AST.Syntax
    import opened Semantics.Equiv
    import opened Semantics.Interp

    type Expr = Syntax.Expr

    const EmptyBlock := Expr.Block([])

    // TODO: move?
    predicate method IsEmptyBlock(e: Expr)
    {
      e.Block? && e.stmts == []
    }

    // TODO: move?
    predicate method IsNonEmptyBlock(e: Expr)
    {
      !(IsEmptyBlock(e))
    }

    predicate Tr_Expr_Post(e: Expr) {
      true
    }

    predicate Tr_Expr_Rel(e: Expr, e': Expr) {
      EqInterp(e, e')
    }
  }

  module FilterEmptyBlocks {
    // Tranformation 1
    
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

    import opened FilterCommon

    type Expr = Syntax.Expr

    function method FilterEmptyBlocks_Seq(es: seq<Expr>): (es': seq<Expr>)
      ensures Seq_All(SupportsInterp, es) ==> Seq_All(SupportsInterp, es')
      ensures |es| >= |es'|
    {
      Seq.Filter(es, IsNonEmptyBlock)
    }

    function method FilterEmptyBlocks_Single(e: Expr): Expr
    {
      if e.Block? then
        Expr.Block(FilterEmptyBlocks_Seq(e.stmts))
      else
        e
    }

    lemma FilterEmptyBlocks_Seq_Rel(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
      requires Seq_All(SupportsInterp, es)
      requires EqState(ctx, ctx')
      ensures EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(FilterEmptyBlocks_Seq(es), env, ctx'))
    {
      reveal InterpBlock_Exprs();
      reveal Seq.Filter();

      var es' := FilterEmptyBlocks_Seq(es);

      var res := InterpBlock_Exprs(es, env, ctx);
      var res' := InterpBlock_Exprs(es', env, ctx');

      // TODO(SMH): there are too many subcases below: I'm pretty sure we can make the proofs in
      // a smarter way.
      if es == [] {
        // Trivial
      }
      else if |es| == 1 {
        assert es == [es[0]];
        reveal InterpExpr();
        reveal InterpBlock();
        if IsEmptyBlock(es[0]) {
          assert es' == [];

          // Interp(es, ctx) == ((), ctx)
          assert InterpBlock_Exprs([es[0]], env, ctx) == InterpExpr(es[0], env, ctx);
          assert InterpExpr(es[0], env, ctx) == InterpBlock_Exprs(es[0].stmts, env, ctx);
          assert InterpBlock_Exprs(es[0].stmts, env, ctx) == Success(Return(V.Unit, ctx));

          // Interp(es', ctx') == ((), ctx')
          assert InterpBlock_Exprs(es', env, ctx') == Success(Return(V.Unit, ctx'));
        }
        else {
          assert es' == es;
          EqInterp_Refl(es[0]);
          EqInterp_Inst(es[0], es[0], env, ctx, ctx');
        }
      }
      else {
        // Case disjunction: is the first expression in the sequence filtered or not?
        if IsEmptyBlock(es[0]) {
          // The first expression is filtered
          var res0 := InterpExpr(es[0], env, ctx);

          // Evaluating the first expression leaves the context unchanged
          assert res0 == Success(Return(V.Unit, ctx)) by {
            reveal InterpExpr();
            reveal InterpBlock();
            // Doesn't work without this assertion
            assert res0 == InterpBlock(es[0].stmts, env, ctx);
            assert es[0].stmts == [];
            // Doesn't work without this assertion
            assert InterpBlock(es[0].stmts, env, ctx) == InterpBlock_Exprs([], env, ctx);
          }

          // Doesn't work without this assertion
          assert res0 == InterpExprWithType(es[0], Types.Unit, env, ctx);

          assert es' == FilterEmptyBlocks_Seq(es[1..]);
          FilterEmptyBlocks_Seq_Rel(es[1..], env, ctx, ctx');
        }
        else {
          // The first expression is not filtered

          EqInterp_Refl(es[0]);
          EqInterp_Inst(es[0], es'[0], env, ctx, ctx');

          var tl := es[1..];
          var tl' := FilterEmptyBlocks_Seq(tl);

          forall env, ctx, ctx' | EqState(ctx, ctx')
            ensures EqInterpResultValue(InterpBlock_Exprs(tl, env, ctx), InterpBlock_Exprs(tl', env, ctx'))
          {
            FilterEmptyBlocks_Seq_Rel(tl, env, ctx, ctx');
          }
          InterpBlock_Exprs_Eq_Append(es[0], es[0], tl, tl', env, ctx, ctx');
        }
      }
    }

    lemma FilterEmptyBlocks_Single_Rel(e: Expr)
      ensures Tr_Expr_Rel(e, FilterEmptyBlocks_Single(e))
    {
      if e.Block? && SupportsInterp(e) {
        reveal SupportsInterp();

        var e' := FilterEmptyBlocks_Single(e);
        var es := e.stmts;

        forall env, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
        {
            FilterEmptyBlocks_Seq_Rel(es, env, ctx, ctx');
            reveal InterpExpr();
            reveal InterpBlock();
        }

        assert SupportsInterp(e');
        assert EqInterp(e, e');
      }
      else {
        EqInterp_Refl(e); 
      }
    }
  }

  module InlineLastBlock {
    // Tranformation 2
    
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

    import opened FilterCommon

    type Expr = Syntax.Expr

    function method InlineLastBlock_Seq(es: seq<Expr>): (es': seq<Expr>)
      ensures Seq_All(SupportsInterp, es) ==> Seq_All(SupportsInterp, es')
      // If the last expression of a sequence of expressions is a block, inline its content.
      //
      // It seems easier to reason about this function if we define it in a recursive way,
      // which is why we do so.
    {
      reveal SupportsInterp();

      // Empty sequence: nothing to do
      if es == [] then
        []
      // We reached the last statement: inline it if it is a block
      else if |es| == 1 then
        if es[0].Block? then
          assert Seq_All(SupportsInterp, es) ==> SupportsInterp(es[0]);
          assert SupportsInterp(es[0]) ==> Seq_All(SupportsInterp, es[0].stmts);
          es[0].stmts
        else
          [es[0]]
      // We haven't reached the last element: recurse on the tail
      else
        [es[0]] + InlineLastBlock_Seq(es[1..])
    }

    function method InlineLastBlock_Single(e: Expr): Expr
    {
      if e.Block? then Expr.Block(InlineLastBlock_Seq(e.stmts))
      else e
    }

    lemma InlineLastBlock_Seq_Rel(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
      requires forall e | e in es :: SupportsInterp(e)
      requires EqState(ctx, ctx')
      ensures forall e | e in InlineLastBlock_Seq(es) :: SupportsInterp(e)
      ensures EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(InlineLastBlock_Seq(es), env, ctx'))
    {
      reveal InterpBlock_Exprs();

      var es' := InlineLastBlock_Seq(es);

      var res := InterpBlock_Exprs(es, env, ctx);
      var res' := InterpBlock_Exprs(es', env, ctx');

      if es == [] {
        // Trivial
      }
      else if |es| == 1 {
        if es[0].Block? {
          reveal InterpExpr();
          reveal InterpBlock();

          // Doesn't work without this assertion - is it because of the fuel?
          assert res == InterpExpr(es[0], env, ctx);
          assert InterpExpr(es[0], env, ctx) == InterpBlock(es[0].stmts, env, ctx);

          assert es' == es[0].stmts;
          InterpBlock_Exprs_Refl(es[0].stmts, env, ctx, ctx');
        }
        else {
          assert es == es';
          InterpBlock_Exprs_Refl(es, env, ctx, ctx');
        }
      }
      else {
        // The first expression appears in both sequences
        EqInterp_Refl(es[0]);
        EqInterp_Inst(es[0], es'[0], env, ctx, ctx');

        // Prove that the sequence concatenations are evaluated in a similar manner
        var tl := es[1..];
        var tl' := InlineLastBlock_Seq(tl);

        forall env, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpBlock_Exprs(tl, env, ctx), InterpBlock_Exprs(tl', env, ctx'))
        {
          InlineLastBlock_Seq_Rel(tl, env, ctx, ctx');
        }
        InterpBlock_Exprs_Eq_Append(es[0], es[0], tl, tl', env, ctx, ctx');
      }
    }

    // Rk.: modulo the names, this is exactly the same proof as for ``FilterEmptyBlocks_Single_Rel``
    lemma InlineLastBlock_Single_Rel(e: Expr)
      ensures Tr_Expr_Rel(e, InlineLastBlock_Single(e))
    {
      if e.Block? && SupportsInterp(e) {
        reveal SupportsInterp();

        var e' := InlineLastBlock_Single(e);
        var es := e.stmts;

        forall env, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
        {
            InlineLastBlock_Seq_Rel(es, env, ctx, ctx');
            reveal InterpExpr();
            reveal InterpBlock();
        }

        assert SupportsInterp(e');
        assert EqInterp(e, e');
      }
      else {
        EqInterp_Refl(e); 
      }
    }
  }

  module SimplifyIfThenElse {
    // Tranformation 3
    
    import Utils.Lib
    import Utils.Lib.Debug
    import opened Utils.Lib.Datatypes
    import opened Transforms.BottomUp

    import opened AST.Syntax
    import opened AST.Predicates
    import opened Semantics.Interp
    import opened Semantics.Values
    import opened Semantics.Equiv
    import opened Semantics.Pure
    import opened Transforms.Generic
    import opened Transforms.Proofs.BottomUp_

    import opened FilterCommon

    type Expr = Syntax.Expr

    function method SimplifyEmptyIfThenElse_Single(e: Expr): Expr
      // Tranformation 3.1: `if b then {} else {} ---> {}`
      //
      // Eliminating `b` might lead to a program which fails less. We might want to be
      // more precise in case we deal with potentially non-terminating programs, for instance
      // by checking that `b` doesn't call any (potentially non-terminating) method.
    {
      // We might want to check that `e.cond` terminates
      if e.If? && IsPure(e.cond) && IsEmptyBlock(e.thn) && IsEmptyBlock(e.els) then EmptyBlock
      else e
    }

    lemma SimplifyEmptyIfThenElse_Single_Rel(e: Expr)
      ensures Tr_Expr_Rel(e, SimplifyEmptyIfThenElse_Single(e))
    {
      if e.If? && IsPure(e.cond) && IsEmptyBlock(e.thn) && IsEmptyBlock(e.els) && SupportsInterp(e) {
        var e' := SimplifyEmptyIfThenElse_Single(e);
        reveal SupportsInterp();

        forall env, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
        {
          var res := InterpExpr(e, env, ctx);
          var res0 := InterpExprWithType(e.cond, Type.Bool, env, ctx);

          if res0.Success? {
            var Return(b, ctx0) := res0.value;

            InterpExprWithType_IsPure_SameState(e.cond, Type.Bool, env, ctx);
            assert ctx0 == ctx;
            
            assert res == InterpExpr(EmptyBlock, env, ctx0) by {
              reveal InterpExpr();
            }

            EqInterp_Refl(EmptyBlock);
            EqInterp_Inst(EmptyBlock, EmptyBlock, env, ctx, ctx');
          }
          else {
            assert res.Failure? by {
              reveal InterpExpr();
            }
          }
        }

        assert SupportsInterp(e');
      }
      else {
        EqInterp_Refl(e);
      }
    }

    // TODO: factorize with ``EliminateNegatedBinops``?
    function method NegateExpr(e: Expr): (e':Expr)
      ensures SupportsInterp(e) ==> SupportsInterp(e')
    {
      reveal SupportsInterp();
      Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [e])
    }

    // TODO: factorize with ``EliminateNegatedBinops``?
    lemma InterpExpr_NegateExpr(e: Expr, env: Environment, ctx: State)
      requires SupportsInterp(e)
      ensures
        match InterpExpr(e, env, ctx)
          case Failure(_) => true
          case Success(Return(v, ctx1)) =>
            match InterpExpr(NegateExpr(e), env, ctx)
            case Failure(_) => !v.Bool?
            case Success(Return(v', ctx1')) =>
              && v.Bool?
              && v'.Bool?
              && v.b == !v'.b
              && ctx1' == ctx1
    {
      var res := InterpExpr(e, env, ctx);
      var e' := NegateExpr(e);
      var res' := InterpExpr(e', env, ctx);

      var args := [e];
      var args_res := InterpExprs(args, env, ctx);
      InterpExprs1_Strong_Eq(e, env, ctx);

      reveal InterpExpr();
      
      if args_res.Success? {
        reveal InterpUnaryOp();
      }
      else {}
    }

    function method NegateIfThenElse_Single(e: Expr): (e': Expr)
      ensures SupportsInterp(e) ==> SupportsInterp(e')
      // Auxiliary transformation: `if b then e0 else e1 ---> if !b then e1 else e0`
    {
      reveal SupportsInterp();
      if e.If? then Expr.If(NegateExpr(e.cond), e.els, e.thn)
      else e
    }
    
    
    lemma NegateIfThenElse_Single_Rel(e: Expr)
      ensures Tr_Expr_Rel(e, NegateIfThenElse_Single(e))
    {
      if e.If? && SupportsInterp(e) {
        var e' := NegateIfThenElse_Single(e);
        
        reveal SupportsInterp();

        forall env, ctx, ctx' | EqState(ctx, ctx')
          ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
        {
          var res := InterpExpr(e, env, ctx);
          var res' := InterpExpr(e', env, ctx);

          var res0 := InterpExprWithType(e.cond, Type.Bool, env, ctx);
          var res0' := InterpExprWithType(e.cond, Type.Bool, env, ctx');

          EqInterp_Refl(e.cond);
          EqInterp_Inst(e.cond, e.cond, env, ctx, ctx');
          
          var res0'' := InterpExprWithType(e'.cond, Type.Bool, env, ctx');
          InterpExpr_NegateExpr(e.cond, env, ctx');

          reveal InterpExpr();
          if res.Success? {
            assert res0'.Success?;
            assert res0''.Success?;

            var Return(b, ctx0) := res0.value;
            var Return(b'', ctx0'') := res0''.value;

            assert b.Bool? && b''.Bool? && b.b == !b''.b;

            EqInterp_Refl(e.thn);
            EqInterp_Inst(e.thn, e.thn, env, ctx0, ctx0'');
            EqInterp_Refl(e.els);
            EqInterp_Inst(e.els, e.els, env, ctx0, ctx0'');
          }
          else {}
        }

        assert SupportsInterp(e');
      }
      else {
        EqInterp_Refl(e);
      }
    }

    function method NegateIfThenElseIfEmptyThen_Single(e: Expr): (e': Expr)
      ensures SupportsInterp(e) ==> SupportsInterp(e')
      // Tranformation 3.2: `if b then {} else e ---> if !b then e else {}`
    {
      reveal SupportsInterp();
      if e.If? && IsEmptyBlock(e.thn) then NegateIfThenElse_Single(e)
      else e
    }

    lemma NegateIfThenElseIfEmptyThen_Single_Rel(e: Expr)
      ensures Tr_Expr_Rel(e, NegateIfThenElseIfEmptyThen_Single(e))
    {
      if e.If? && IsEmptyBlock(e.thn) {
        NegateIfThenElse_Single_Rel(e);
      }
      else {
        EqInterp_Refl(e);
      }
    }

    function method Simplify_Single(e: Expr): (e': Expr)
      ensures SupportsInterp(e) ==> SupportsInterp(e')
      ensures Tr_Expr_Rel(e, e')
      // The full transformation 3
    {
      reveal SupportsInterp();
      var e1 := SimplifyEmptyIfThenElse_Single(e);
      SimplifyEmptyIfThenElse_Single_Rel(e);
      var e2 := NegateIfThenElseIfEmptyThen_Single(e1);
      NegateIfThenElseIfEmptyThen_Single_Rel(e1);
      EqInterp_Trans(e, e1, e2);
      e2
    } 
  }

  module Simplify {
    /// The final transformation
    
    import Utils.Lib
    import Utils.Lib.Debug
    import opened Utils.Lib.Datatypes
    import opened Transforms.BottomUp

    import opened AST.Syntax
    import opened AST.Predicates
    import opened Semantics.Interp
    import opened Semantics.Values
    import opened Semantics.Equiv
    import opened Semantics.Pure
    import opened Transforms.Generic
    import opened Transforms.Proofs.BottomUp_

    import opened FilterCommon
    import FilterEmptyBlocks
    import InlineLastBlock
    import SimplifyIfThenElse

    type Expr = Syntax.Expr

    function method Simplify_Single(e: Expr): (e': Expr)
      ensures SupportsInterp(e) ==> SupportsInterp(e')
      ensures EqInterp(e, e')
      // This function puts all the transformation together
    {
      var e1 := FilterEmptyBlocks.FilterEmptyBlocks_Single(e);
      FilterEmptyBlocks.FilterEmptyBlocks_Single_Rel(e);
      assert EqInterp(e, e1);
      var e2 := InlineLastBlock.InlineLastBlock_Single(e1);
      InlineLastBlock.InlineLastBlock_Single_Rel(e1);
      assert EqInterp(e1, e2);
      var e3 := SimplifyIfThenElse.Simplify_Single(e2);
      assert EqInterp(e2, e3);

      EqInterp_Trans(e, e1, e2);
      EqInterp_Trans(e, e2, e3);
      assert EqInterp(e, e3);

      e3
    }

    predicate Tr_Pre(p: Program) {
      true
    }

    predicate Tr_Expr_Post(e: Exprs.T) {
      true
    }

    predicate Tr_Post(p: Program)
    {
      Deep.All_Program(p, Tr_Expr_Post)
    }

    const Tr_Expr : BottomUpTransformer :=
      ( Deep.All_Expr_True_Forall(Tr_Expr_Post);
        assert IsBottomUpTransformer(Simplify_Single, Tr_Expr_Post);
        TR(Simplify_Single,
           Tr_Expr_Post))

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
      Deep.All_Expr_True_Forall(Tr_Expr.f.requires);
      assert Deep.All_Method(m, Tr_Expr.f.requires);
      EqInterp_Lift(Tr_Expr.f);
      Map_Method_PreservesRel(m, Tr_Expr, Tr_Expr_Rel);
      Map_Method(m, Tr_Expr)
    }

    function method Apply(p: Program) : (p': Program)
      requires Tr_Pre(p)
      ensures Tr_Post(p')
      ensures Tr_Expr_Rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
      // Apply the transformation to a program.
    {
      Deep.All_Expr_True_Forall(Tr_Expr.f.requires);
      assert Deep.All_Program(p, Tr_Expr.f.requires);
      EqInterp_Lift(Tr_Expr.f);
      Map_Program_PreservesRel(p, Tr_Expr, Tr_Expr_Rel);
      Map_Program(p, Tr_Expr)
    }
  }
}

include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "../Utils/StrTree.dfy"
include "../Semantics/Interp.dfy"
include "../Semantics/Equiv.dfy"
include "../Transforms/Generic.dfy"
include "../Transforms/Shallow.dfy"

module Bootstrap.Transforms.BottomUp {
      import opened AST.Syntax
      import opened Utils.Lib
      import opened AST.Predicates
      import opened Semantics.Equiv
      import opened Generic
      import Shallow

      predicate MapChildrenPreservesPre(f: Expr --> Expr, post: Expr -> bool)
      // This predicate gives us the conditions for which, if we deeply apply `f` to all
      // the children of an expression, then the resulting expression satisfies the pre
      // of `f` (i.e., we can call `f` on it).
      //
      // Given `e`, `e'`, if:
      // - `e` and `e'` have the same constructor
      // - `e` satisfies the pre of `f`
      // - all the children of `e'` deeply satisfy the post of `f`
      // Then:
      // - `e'` satisfies the pre of `f`
      {
        forall e, e' ::
           && Exprs.ConstructorsMatch(e, e')
           && f.requires(e)
           && Deep.AllChildren_Expr(e', post)
           ==> f.requires(e')
      }

      predicate TransformerMatchesPrePost(f: Expr --> Expr, post: Expr -> bool)
      // This predicate gives us the conditions for which, if we deeply apply `f` to an
      // expression, the resulting expression satisfies the postcondition we give for `f`.
      //
      // Given `e`, if:
      // - all the children of `e` deeply satisfy the post of `f`
      // - `e` satisfies the pre of `f`
      // Then:
      // - `f(e)` deeply satisfies the post of `f`
      {
        forall e: Expr | Deep.AllChildren_Expr(e, post) && f.requires(e) ::
          Deep.All_Expr(f(e), post)
      }

      // FIXME(CPC) move?
      predicate TransformerShallowPreservesRel(f: Expr --> Expr, rel: (Expr, Expr) -> bool)
      // `f` relates its input and its output with `rel`.
      {
        forall e | f.requires(e) :: rel(e, f(e))
      }

      predicate TransformerDeepPreservesRel(f: Expr --> Expr, rel: (Expr, Expr) -> bool)
      // This predicate is quite general, but is to be used in the following setting:
      // if we apply `f` on all the children of `e`, leading to an expression `e'`, then we
      // can relate `e` and `f(e')` with `rel`.
      {
        forall e, e' ::
           && Exprs.ConstructorsMatch(e, e')
           && f.requires(e')
           && All_Rel_Forall(rel, e.Children(), e'.Children())
           ==> rel(e, f(e'))
      }

      predicate IsBottomUpTransformer(f: Expr --> Expr, post: Expr -> bool, rel: (Expr,Expr) -> bool)
      // Predicate for ``BottomUpTransformer``
      {
        && TransformerMatchesPrePost(f, post)
        && MapChildrenPreservesPre(f, post)
        && TransformerDeepPreservesRel(f, rel)
      }

      // Identity bottom-up transformer: we need it only because we need a witness when
      // defining ``BottomUpTransformer``, to prove that the type is inhabited.
      const IdentityTransformer: ExprTransformer :=
        TR(d => d, _ => true, (_,_) => true)

      lemma IdentityMatchesPrePost()
        ensures TransformerMatchesPrePost(IdentityTransformer.f, IdentityTransformer.post)
      { }

      lemma IdentityPreservesPre()
        ensures MapChildrenPreservesPre(IdentityTransformer.f, IdentityTransformer.post)
      { }

      lemma IdentityPreservesRel()
        ensures TransformerDeepPreservesRel(IdentityTransformer.f, IdentityTransformer.rel)
      { }

      // FIXME(CPC): Move to equivs (use a datatype to make this a member function)
      predicate RelCanBeMapLifted(rel: (Expr, Expr) -> bool)
      // In many situations, the binary relation between the input and the output is transitive
      // and can be lifted through the map function.
      {
        forall e, e' ::
           && Exprs.ConstructorsMatch(e, e')
           && All_Rel_Forall(rel, e.Children(), e'.Children())
           ==> rel(e, e')
      }

      // A bottom-up transformer, i.e.: a transformer we can recursively apply bottom-up to
      // an expression, and get the postcondition we expect on the resulting expression.
      type BottomUpTransformer = tr: ExprTransformer | IsBottomUpTransformer(tr.f, tr.post, tr.rel)
        witness (IdentityMatchesPrePost();
                 IdentityPreservesPre();
                 IdentityPreservesRel();
                 IdentityTransformer)

      predicate TODO() { false }

      function method MapChildren_Expr(e: Expr, tr: BottomUpTransformer) :
        (e': Expr)
        decreases e, 0
        requires Deep.AllChildren_Expr(e, tr.f.requires)
        ensures Deep.AllChildren_Expr(e', tr.post)
        ensures Exprs.ConstructorsMatch(e, e')
        ensures All_Rel_Forall(tr.rel, e.Children(), e'.Children())
      // Apply a transformer bottom-up on the children of an expression.
      {
        // Not using datatype updates below to ensure that we get a warning if a
        // type gets new arguments
        match e {
          case Var(_) => e
          case Literal(lit_) => e
          case Abs(vars, body) => Expr.Abs(vars, Map_Expr(body, tr))
          case Apply(aop, exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            var e' := Expr.Apply(aop, exprs');
            assert Exprs.ConstructorsMatch(e, e');
            e'
          case Block(exprs) =>
            var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
            Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
            var e' := Expr.Block(exprs');
            assert Exprs.ConstructorsMatch(e, e');
            e'
          case Bind(vars, vals, body) =>
            assume TODO();
            var vals' := Seq.Map(e requires e in vals => Map_Expr(e, tr), vals);
            Map_All_IsMap(e requires e in vals => Map_Expr(e, tr), vals);
            var e' := Expr.Bind(vars, vals', Map_Expr(body, tr));
            assert Exprs.ConstructorsMatch(e, e');
            e'
          case If(cond, thn, els) =>
            var e' := Expr.If(Map_Expr(cond, tr), Map_Expr(thn, tr), Map_Expr(els, tr));
            assert Exprs.ConstructorsMatch(e, e');
            e'
        }
      }

      // Apply a transformer bottom-up on an expression.
      function method Map_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
        decreases e, 1
        requires Deep.All_Expr(e, tr.f.requires)
        ensures Deep.All_Expr(e', tr.post)
      {
        Deep.AllImpliesChildren(e, tr.f.requires);
        tr.f(MapChildren_Expr(e, tr))
      }

      function method Map_Expr_Transformer'(tr: BottomUpTransformer) :
        (tr': Transformer_<Expr,Expr>)
      // We can write aggregated statements only in lemmas.
      // This forced me to cut this definition into pieces...
      {
        TR(e requires Deep.All_Expr(e, tr.f.requires) => Map_Expr(e, tr),
           e' => Deep.All_Expr(e', tr.post),
           tr.rel)
      }

      lemma Map_Expr_Transformer'_Lem(tr: BottomUpTransformer)
        ensures Map_Expr_Transformer'(tr).HasValidRel()
      {
        var tr' := Map_Expr_Transformer'(tr);
        forall e:Expr
          ensures tr'.f.requires(e) ==> tr.rel(e, tr'.f(e))
        {
          if tr'.f.requires(e) {
            var e2 := tr'.f(e);
            match e {
              case Var(_) => {}
              case Literal(_) => {}
              case Abs(vars, body) =>
                assert tr.rel(e, tr'.f(e));
              case Apply(applyOp, args) =>
                assert tr.rel(e, tr'.f(e));
              case Block(stmts) =>
                assert tr.rel(e, tr'.f(e));
              case Bind(vars, vals, body) =>
                assert tr.rel(e, tr'.f(e));
              case If(cond, thn, els) => {
                assert tr.rel(e, tr'.f(e));
              }
            }
          }
        }
      }

      function method Map_Expr_Transformer(tr: BottomUpTransformer) :
        (tr': ExprTransformer)
      // Given a bottom-up transformer `tr`, return a transformer which applies `tr` in
      // a bottom-up manner.
      {
        var tr': Transformer_<Expr,Expr> := Map_Expr_Transformer'(tr);
        Map_Expr_Transformer'_Lem(tr);
        tr'
      }

      function method {:opaque} Map_Method(m: Method, tr: BottomUpTransformer) :
        (m': Method)
        requires Deep.All_Method(m, tr.f.requires)
        ensures Deep.All_Method(m', tr.post)
        ensures tr.rel(m.methodBody, m'.methodBody)
      // Apply a transformer to a method, in a bottom-up manner.
      {
        Shallow.Map_Method(m, Map_Expr_Transformer(tr))
      }

      function method {:opaque} Map_Program(p: Program, tr: BottomUpTransformer) :
        (p': Program)
        requires Deep.All_Program(p, tr.f.requires)
        ensures Deep.All_Program(p', tr.post)
        ensures tr.rel(p.mainMethod.methodBody, p'.mainMethod.methodBody)
      // Apply a transformer to a program, in a bottom-up manner.
      {
        Shallow.Map_Program(p, Map_Expr_Transformer(tr))
      }
}

module Bootstrap.Transforms.Proofs.BottomUp_ {
    // BUG(https://github.com/dafny-lang/dafny/issues/2012)
    import Utils.Lib
    import Utils.Lib.Debug
    import opened AST.Syntax
    import opened Utils.Lib.Datatypes
    import opened BottomUp

    import opened AST.Predicates
    import opened Generic
    import opened Semantics.Interp
    import opened Semantics.Values
    import opened Semantics.Equiv


    type Expr = Syntax.Expr
    type WV = Interp.Value // FIXME
    type EqWV = Interp.EqWV // FIXME
    type Context = Values.Context

    // TODO: maybe not necessary to make this opaque
    // FIXME(CPC): Change to Interp.Expr and remove SupportsInterp below
    predicate {:opaque} EqInterp_CanBeMapLifted_Pre(e: Expr, e': Expr, env: Environment, ctx: State, ctx': State)
    {
      && EqState(ctx, ctx')
      && Exprs.ConstructorsMatch(e, e')
      && All_Rel_Forall(EqInterp, e.Children(), e'.Children())
      && SupportsInterp(e) // TODO: remove (`Expr` is now a subset type)
      && SupportsInterp(e') // TODO: remove (`Expr` is now a subset type)
    }

    // TODO: maybe not necessary to make this opaque
    predicate {:opaque} EqInterp_CanBeMapLifted_Post(e: Expr, e': Expr, env: Environment, ctx: State, ctx': State)
      requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
    }

    lemma EqInterp_Expr_CanBeMapLifted_Lem(e: Expr, e': Expr, env: Environment, ctx: State, ctx': State)
      requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
      decreases e, env, 1
    {
      // Note that we don't need to reveal ``InterpExpr``: we just match on the first
      // expression and call the appropriate auxiliary lemma.

      // We need to retrieve some information from the pre:
      // - `SupportsInterp(e)` is necessary to prove that we can't get in the last branch
      //   of the match
      // - `Exprs.ConstructorsMatch(e, e')` is necessary for the lemma preconditions
      assert SupportsInterp(e) && SupportsInterp(e') && Exprs.ConstructorsMatch(e, e') by {
        reveal EqInterp_CanBeMapLifted_Pre();
      }

      match e {
        case Var(_) => {
          EqInterp_Expr_Var_CanBeMapLifted_Lem(e, e', env, ctx, ctx');
        }
        case Literal(_) => {
          EqInterp_Expr_Literal_CanBeMapLifted_Lem(e, e', env, ctx, ctx');
        }
        case Abs(_, _) => {
          EqInterp_Expr_Abs_CanBeMapLifted_Lem(e, e', env, ctx, ctx');
        }
        case Apply(Lazy(_), _) => {
          EqInterp_Expr_ApplyLazy_CanBeMapLifted_Lem(e, e', env, ctx, ctx');
        }
        case Apply(Eager(_), _) => {
          EqInterp_Expr_ApplyEager_CanBeMapLifted_Lem(e, e', env, ctx, ctx');
        }
        case If(_, _, _) => {
          EqInterp_Expr_If_CanBeMapLifted_Lem(e, e', env, ctx, ctx');
        }
        case Bind(_, _, _) => {
          assume TODO();
        }
        case Block(_) => {
          EqInterp_Expr_Block_CanBeMapLifted_Lem(e, e', env, ctx, ctx');
        }
        case _ => {
          // Unsupported branch
          reveal SupportsInterp(); // We need this to see that some variants are not supported
          assert false;
        }
      }
    }

    lemma EqInterp_Expr_Var_CanBeMapLifted_Lem(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
      requires e.Var?
      requires e'.Var?
      requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
      decreases e, env, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal TryGetVariable();
      reveal GEqCtx();

      assume TODO();
    }

    // FIXME(CPC): Can this lemma and the following ones use Interp.Expr?
    lemma EqInterp_Expr_Literal_CanBeMapLifted_Lem(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
      requires e.Literal?
      requires e'.Literal?
      requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
      decreases e, env, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal InterpLiteral();
    }

    lemma EqInterp_Expr_Abs_CanBeMapLifted_Lem(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
      requires e.Abs?
      requires e'.Abs?
      requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
      decreases e, env, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      var Abs(vars, body) := e;
      var Abs(vars', body') := e';
      assert vars == vars';
      assert body == e.Children()[0];
      assert body' == e'.Children()[0];
      assert EqInterp(body, body');

      var cv := Closure(ctx.locals, vars, body);
      var cv' := Closure(ctx'.locals, vars', body');
      assert InterpExpr(e, env, ctx) == Success(Return(cv, ctx)) by { reveal InterpExpr(); }
      assert InterpExpr(e', env, ctx') == Success(Return(cv', ctx')) by {reveal InterpExpr(); }

      forall env: Environment, argvs: seq<WV>, argvs': seq<WV> |
        && |argvs| == |argvs'| == |vars|
        && (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
        ensures
          var res := InterpCallFunctionBody(cv, env, argvs);
          var res' := InterpCallFunctionBody(cv', env, argvs');
          EqPureInterpResultValue(res, res') {
        EqInterp_Expr_AbsClosure_CanBeMapLifted_Lem(cv, cv', env, argvs, argvs');
      }

      assert EqValue_Closure(cv, cv') by {
        reveal EqValue_Closure();
      }
    }

    lemma EqInterp_Expr_AbsClosure_CanBeMapLifted_Lem(cv: WV, cv': WV, env: Environment, argvs: seq<WV>, argvs': seq<WV>)
      requires cv.Closure?
      requires cv'.Closure?
      requires |argvs| == |argvs'| == |cv.vars|
      requires (forall i | 0 <= i < |argvs| :: EqValue(argvs[i], argvs'[i]))
      requires cv.vars == cv'.vars
      requires EqCtx(cv.ctx, cv'.ctx)
      requires EqInterp(cv.body, cv'.body)
      ensures
          var res := InterpCallFunctionBody(cv, env, argvs);
          var res' := InterpCallFunctionBody(cv', env, argvs');
          EqPureInterpResultValue(res, res')
    {
      var res := InterpCallFunctionBody(cv, env, argvs);
      var res' := InterpCallFunctionBody(cv', env, argvs');

      var ctx1 := BuildCallState(cv.ctx, cv.vars, argvs);
      var ctx1' := BuildCallState(cv'.ctx, cv'.vars, argvs');
      BuildCallState_EqState_Lem(cv.ctx, cv'.ctx, cv.vars, argvs, argvs');
      assert EqState(ctx1, ctx1');

      assert EqPureInterpResultValue(res, res') by {
        reveal InterpCallFunctionBody();
      }
    }

    lemma EqInterp_Expr_ApplyLazy_CanBeMapLifted_Lem(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
      requires e.Apply? && e.aop.Lazy?
      requires e'.Apply? && e'.aop.Lazy?
      requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
      decreases e, env, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal InterpLazy();

      reveal SupportsInterp();

      var res := InterpExpr(e, env, ctx);
      var res' := InterpExpr(e', env, ctx');

      assert res == InterpLazy(e, env, ctx);
      assert res' == InterpLazy(e', env, ctx');

      // Both expressions should be booleans
      var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
      var op', e0', e1' := e'.aop.lOp, e'.args[0], e'.args[1];
      assert op == op';

      // Evaluate the first boolean
      EqInterp_Lem(e0, e0', env, ctx, ctx');
      var res0 := InterpExprWithType(e0, Type.Bool, env, ctx);
      var res0' := InterpExprWithType(e0', Type.Bool, env, ctx');
      assert EqInterpResultValue(res0, res0');

      match res0 {
        case Success(Return(v0, ctx0)) => {
          var Return(v0', ctx0') := res0'.value;

          EqInterp_Lem(e1, e1', env, ctx0, ctx0');
          // The proof fails if we don't introduce res1 and res1'
          var res1 := InterpExprWithType(e1, Type.Bool, env, ctx0);
          var res1' := InterpExprWithType(e1', Type.Bool, env, ctx0');
          assert EqInterpResultValue(res1, res1');
          assert EqInterpResultValue(res, res');
        }
        case Failure(_) => {
          assert res0'.Failure?;
          assert EqInterpResultValue(res, res');
        }
      }
    }

    lemma EqInterp_Expr_ApplyEager_CanBeMapLifted_Lem(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
      requires e.Apply? && e.aop.Eager?
      requires e'.Apply? && e'.aop.Eager?
      requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
      decreases e, env, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal SupportsInterp();

      var res := InterpExpr(e, env, ctx);
      var res' := InterpExpr(e', env, ctx');

      var Apply(Eager(op), args) := e;
      var Apply(Eager(op'), args') := e';

      // The arguments evaluate to similar results
      var res0 := InterpExprs(args, env, ctx);
      var res0' := InterpExprs(args', env, ctx');
      InterpExprs_EqInterp_Lem(args, args', env, ctx, ctx');
      assert EqInterpResult(EqSeqValue, res0, res0');

      match (res0, res0') {
        case (Success(res0), Success(res0')) => {
          // Dafny crashes if we try to deconstruct the `Return`s in the match.
          // See: https://github.com/dafny-lang/dafny/issues/2258
          var Return(argvs, ctx0) := res0;
          var Return(argvs', ctx0') := res0';

          match (op, op') {
            case (UnaryOp(op), UnaryOp(op')) => {
              assert op == op';
              EqInterp_Expr_UnaryOp_CanBeMapLifted_Lem(e, e', op, argvs[0], argvs'[0]);
              assert EqInterpResultValue(res, res');
            }
            case (BinaryOp(bop), BinaryOp(bop')) => {
              assert bop == bop';
              EqInterp_Expr_BinaryOp_CanBeMapLifted_Lem(e, e', bop, argvs[0], argvs[1], argvs'[0], argvs'[1]);
              assert EqInterpResultValue(res, res');
            }
            case (TernaryOp(top), TernaryOp(top')) => {
              assert top == top';
              EqInterp_Expr_TernaryOp_CanBeMapLifted_Lem(e, e', top, argvs[0], argvs[1], argvs[2], argvs'[0], argvs'[1], argvs'[2]);
              assert EqInterpResultValue(res, res');
            }
            case (Builtin(Display(ty)), Builtin(Display(ty'))) => {
              assert ty == ty';
              EqInterp_Expr_Display_CanBeMapLifted_Lem(e, e', ty.kind, argvs, argvs');
              assert EqInterpResultValue(res, res');
            }
            case (FunctionCall(), FunctionCall()) => {
              EqInterp_Expr_FunctionCall_CanBeMapLifted_Lem(e, e', env, argvs[0], argvs'[0], argvs[1..], argvs'[1..]);
              assert EqInterpResultValue(res, res');
            }
            case _ => {
              // Impossible branch
              assert false;
            }
          }
        }
        case (Failure(_), Failure(_)) => {
          assert res.Failure?;
          assert res'.Failure?;
          assert EqInterpResultValue(res, res');
        }
        case _ => {
          // Impossible branch
          assert false;
        }
      }
    }

    // TODO: e and e' should be the same actually
    lemma EqInterp_Expr_UnaryOp_CanBeMapLifted_Lem(
      e: Interp.Expr, e': Interp.Expr, op: UnaryOp, v: WV, v': WV
    )
      requires !op.MemberSelect?
      requires EqValue(v, v')
      ensures EqPureInterpResultValue(InterpUnaryOp(e, op, v), InterpUnaryOp(e', op, v'))
    {
      reveal InterpUnaryOp();

      var res := InterpUnaryOp(e, op, v);
      var res' := InterpUnaryOp(e', op, v');

      // We make a case disjunction on the final result so as to get
      // information from the fact that the calls to ``Need`` succeeded.
      // The Failure case is trivial.
      if res.Success? {
        match op {
          case BVNot => {
            assert v.BitVector?;
            assert v'.BitVector?;
          }
          case BoolNot => {
            assert v.Bool?;
            assert v'.Bool?;
          }
          case SeqLength => {
            assert v.Seq?;
            assert v'.Seq?;
            assert |v.sq| == |v'.sq|;
          }
          case SetCard => {
            assert v.Set?;
            assert v'.Set?;
            assert |v.st| == |v'.st|;
          }
          case MultisetCard => {
            assert v.Multiset?;
            assert v'.Multiset?;
            assert |v.ms| == |v'.ms|;
          }
          case MapCard => {
            assert v.Map?;
            assert v'.Map?;
            assert |v.m| == |v'.m|;
          }
          case _ => {
            // Impossible branch
            assert false;
          }
        }
      }
      else {
        assert EqPureInterpResultValue(res, res');
      }
    }

    // TODO: we could split this lemma, whose proof is big (though straightforward),
    // but it is a bit annoying to do...
    // TODO: e and e' should be the same actually
    lemma EqInterp_Expr_BinaryOp_CanBeMapLifted_Lem(
      e: Interp.Expr, e': Interp.Expr, bop: BinaryOp, v0: WV, v1: WV, v0': WV, v1': WV
    )
      requires !bop.BV? && !bop.Datatypes?
      requires EqValue(v0, v0')
      requires EqValue(v1, v1')
      ensures EqPureInterpResultValue(InterpBinaryOp(e, bop, v0, v1), InterpBinaryOp(e', bop, v0', v1'))
    {
      reveal InterpBinaryOp();

      var res := InterpBinaryOp(e, bop, v0, v1);
      var res' := InterpBinaryOp(e', bop, v0', v1');

      // Below: for the proofs about binary operations involving collections (Set, Map...),
      // see the Set case, which gives the general strategy.
      match bop {
        case Numeric(op) => {
          assert EqPureInterpResultValue(res, res');
        }
        case Logical(op) => {
          assert EqPureInterpResultValue(res, res');
        }
        case Eq(op) => {
          // The proof strategy is similar to the Set case.
          EqValue_HasEqValue_Eq_Lem(v0, v0');
          EqValue_HasEqValue_Eq_Lem(v1, v1');

          // If the evaluation succeeded, it means the calls to ``Need``
          // succeeded, from which we can derive information.
          if res.Success? {
            assert EqPureInterpResultValue(res, res');
          }
          else {
            // trivial
          }
        }
        case Char(op) => {
          assert EqPureInterpResultValue(res, res');
        }
        case Sets(op) => {
          // We make a case disjunction between the "trivial" operations,
          // and the others. We treat the "difficult" operations first.
          // In the case of sets, the trivial operations are those which
          // take two sets as parameters (they are trivial, because if
          // two set values are equivalent according to ``EqValue``, then
          // they are actually equal for ``==``).
          if op.InSet? || op.NotInSet? {
            // The trick is that:
            // - either v0 and v0' have a decidable equality, in which case
            //   the evaluation succeeds, and we actually have that v0 == v0'.
            // - or they don't, in which case the evaluation fails.
            // Of course, we need to prove that v0 has a decidable equality
            // iff v0' has one. The important results are given by the lemma below.
            EqValue_HasEqValue_Eq_Lem(v0, v0');

            if res.Success? {
              assert res'.Success?;

              // If the evaluation succeeded, it means the calls to ``Need``
              // succeeded, from which we can derive information, in particular
              // information about the equality between values, which allows us
              // to prove the goal.
              assert HasEqValue(v0);
              assert HasEqValue(v0');
              assert v0 == v0';

              assert v1.Set?;
              assert v1'.Set?;
              assert v1 == v1';

              assert EqPureInterpResultValue(res, res');
            }
            else {
              // This is trivial
            }
          }
          else {
            // All the remaining operations are performed between sets.
            // ``EqValue`` is true on sets iff they are equal, so
            // this proof is trivial.

            // We enumerate all the cases on purpose, so that this assertion fails
            // if we add more cases, making debugging easier.
            assert || op.SetEq? || op.SetNeq? || op.Subset? || op.Superset? || op.ProperSubset?
                   || op.ProperSuperset? || op.Disjoint? || op.Union? || op.Intersection?
                   || op.SetDifference?;
            assert EqPureInterpResultValue(res, res');
          }
        }
        case Multisets(op) => {
          // Rk.: this proof is similar to the one for Sets
          if op.InMultiset? || op.NotInMultiset? {
            EqValue_HasEqValue_Eq_Lem(v0, v0');
          }
          else if op.MultisetSelect? {
            // Rk.: this proof is similar to the one for Sets
            EqValue_HasEqValue_Eq_Lem(v1, v1');
          }
          else {
            // All the remaining operations are performed between multisets.
            // ``EqValue`` is true on sets iff they are equal, so
            // this proof is trivial.

            // Same as for Sets: we enumerate all the cases on purpose
            assert || op.MultisetEq? || op.MultisetNeq? || op.MultiSubset? || op.MultiSuperset?
                   || op.ProperMultiSubset? || op.ProperMultiSuperset? || op.MultisetDisjoint?
                   || op.MultisetUnion? || op.MultisetIntersection? || op.MultisetDifference?;

            assert EqPureInterpResultValue(res, res');
          }
        }
        case Sequences(op) => {
          // Rk.: the proof strategy is given by the Sets case
          EqValue_HasEqValue_Eq_Lem(v0, v0');
          EqValue_HasEqValue_Eq_Lem(v1, v1');

          if op.SeqDrop? || op.SeqTake? {
            if res.Success? {
              assert res'.Success?;

              var len := |v0.sq|;
              // Doesn't work without this assertion
              assert forall i | 0 <= i < len :: EqValue(v0.sq[i], v0'.sq[i]);
              assert EqPureInterpResultValue(res, res');
            }
            else {
              // Trivial
            }
          }
          else {
            // Same as for Sets: we enumerate all the cases on purpose
            assert || op.SeqEq? || op.SeqNeq? || op.Prefix? || op.ProperPrefix? || op.Concat?
                   || op.InSeq? || op.NotInSeq? || op.SeqSelect?;

            assert EqPureInterpResultValue(res, res');
          }
        }
        case Maps(op) => {
          // Rk.: the proof strategy is given by the Sets case
          EqValue_HasEqValue_Eq_Lem(v0, v0');
          EqValue_HasEqValue_Eq_Lem(v1, v1');

          if op.MapEq? || op.MapNeq? || op.InMap? || op.NotInMap? || op.MapSelect? {
            assert EqPureInterpResultValue(res, res');
          }
          else {
            assert op.MapMerge? || op.MapSubtraction?;

            // Z3 needs a bit of help to prove the equivalence between the maps

            if res.Success? {
              assert res'.Success?;

              // The evaluation succeeds, and returns a map
              var m1 := res.value.m;
              var m1' := res'.value.m;

              // Prove that: |m1| == |m1'|
              assert m1.Keys == m1'.Keys;
              assert |m1| == |m1.Keys|; // This is necessary
              assert |m1'| == |m1'.Keys|; // This is necessary

              assert EqPureInterpResultValue(res, res');
            }
            else {
              // Trivial
            }
          }
        }
      }
    }

    // TODO: e and e' should be the same actually
    lemma EqInterp_Expr_TernaryOp_CanBeMapLifted_Lem(
      e: Interp.Expr, e': Interp.Expr, top: TernaryOp, v0: WV, v1: WV, v2: WV, v0': WV, v1': WV, v2': WV
    )
      requires EqValue(v0, v0')
      requires EqValue(v1, v1')
      requires EqValue(v2, v2')
      ensures EqPureInterpResultValue(InterpTernaryOp(e, top, v0, v1, v2), InterpTernaryOp(e', top, v0', v1', v2'))
    {
      reveal InterpTernaryOp();

      var res := InterpTernaryOp(e, top, v0, v1, v2);
      var res' := InterpTernaryOp(e', top, v0', v1', v2');

      match top {
        case Sequences(op) => {}
        case Multisets(op) => {
          EqValue_HasEqValue_Eq_Lem(v1, v1');
        }
        case Maps(op) => {
          EqValue_HasEqValue_Eq_Lem(v1, v1');
        }
      }
    }

    lemma EqInterp_Expr_Display_CanBeMapLifted_Lem(
      e: Interp.Expr, e': Interp.Expr, kind: Types.CollectionKind, vs: seq<WV>, vs': seq<WV>
    )
      requires EqSeqValue(vs, vs')
      ensures EqPureInterpResultValue(InterpDisplay(e, kind, vs), InterpDisplay(e', kind, vs'))
    {
      reveal InterpDisplay();

      var res := InterpDisplay(e, kind, vs);
      var res' := InterpDisplay(e', kind, vs');

      match kind {
        case Map(_) => {
          InterpMapDisplay_EqArgs_Lem(e, e', vs, vs');
          assert EqPureInterpResultValue(res, res');
        }
        case Multiset => {
          EqValue_HasEqValue_Eq_Forall_Lem();
          if res.Success? {
            assert res'.Success?;
            assert (forall i | 0 <= i < |vs| :: HasEqValue(vs[i]));
            assert (forall i | 0 <= i < |vs| :: HasEqValue(vs'[i]));
            assert (forall i | 0 <= i < |vs| :: EqValue(vs[i], vs'[i]));
            assert vs == vs';
            assert EqPureInterpResultValue(res, res');
          }
          else {}
        }
        case Seq => {
          assert EqPureInterpResultValue(res, res');
        }
        case Set => {
          EqValue_HasEqValue_Eq_Forall_Lem();
          assert EqPureInterpResultValue(res, res');
        }
      }
    }

    lemma EqInterp_Expr_FunctionCall_CanBeMapLifted_Lem(
      e: Interp.Expr, e': Interp.Expr, env: Environment, f: WV, f': WV, argvs: seq<WV>, argvs': seq<WV>
    )
      requires EqValue(f, f')
      requires EqSeqValue(argvs, argvs')
      ensures EqPureInterpResultValue(InterpFunctionCall(e, env, f, argvs),
                                      InterpFunctionCall(e', env, f', argvs'))
    {
      var res := InterpFunctionCall(e, env, f, argvs);
      var res' := InterpFunctionCall(e', env, f', argvs');

      if res.Success? || res'.Success? {
        assume TODO();

        reveal InterpFunctionCall();
        reveal InterpCallFunctionBody();
        reveal EqValue_Closure();

        var Closure(ctx, vars, body) := f;
        var Closure(ctx', vars', body') := f';
        assert |vars| == |vars'|;

        // We have restrictions on the arguments on which we can apply the equivalence relation
        // captured by ``EqValue_Closure``. We do the assumption that, if one of the calls succeedeed,
        // then the arguments are "not too big" and we can apply the equivalence. This would be true
        // if the program was successfully type-checked.
        assume (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs[i]) < ValueTypeHeight(f));
        assume (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs'[i]) < ValueTypeHeight(f'));

        var res0 := InterpCallFunctionBody(f, env.(fuel := env.fuel - 1), argvs);
        var res0' := InterpCallFunctionBody(f', env.(fuel := env.fuel - 1), argvs');
        // This comes from EqValue_Closure
        assert EqPureInterpResultValue(res0, res0');

        // By definition
        assert res0 == res;
        assert res0' == res';

        assert EqPureInterpResultValue(res, res');
      }
      else {
        assert res.Failure? && res'.Failure?;
      }
    }

    lemma EqInterp_Expr_If_CanBeMapLifted_Lem(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
      requires e.If?
      requires e'.If?
      requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
      decreases e, env, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal SupportsInterp();

      var res := InterpExpr(e, env, ctx);
      var res' := InterpExpr(e', env, ctx');

      var If(cond, thn, els) := e;
      var If(cond', thn', els') := e';

      assert cond == e.Children()[0];
      assert thn == e.Children()[1];
      assert els == e.Children()[2];

      assert cond' == e'.Children()[0];
      assert thn' == e'.Children()[1];
      assert els' == e'.Children()[2];

      assert EqInterp(cond, cond');
      assert EqInterp(thn, thn');
      assert EqInterp(els, els');

      assert SupportsInterp(e');

      var res0 := InterpExprWithType(cond, Type.Bool, env, ctx);
      var res0' := InterpExprWithType(cond', Type.Bool, env, ctx');

      EqInterp_Lem(cond, cond', env, ctx, ctx');
      assert EqInterpResultValue(res0, res0');

      if res0.Success? {
        var Return(condv, ctx0) := res0.value;
        var Return(condv', ctx0') := res0'.value;

        EqInterp_Lem(thn, thn', env, ctx0, ctx0'); // Proof fails without this
        EqInterp_Lem(els, els', env, ctx0, ctx0'); // Proof fails without this
      }
      else {
        // Trivial
      }
    }

    // We can't use the type `seq<Interp.Expr>` for `es` and `es'`, because then Dafny is unable to
    // prove the requires clauses.
    lemma EqInterp_Expr_BlockExprs_CanBeMapLifted_Lem(es: seq<Exprs.T>, es': seq<Exprs.T>, env: Environment, ctx: State, ctx': State)
      requires EqState(ctx, ctx')
      requires All_Rel_Forall(EqInterp, es, es')
      requires forall e | e in es :: SupportsInterp(e)
      requires forall e | e in es' :: SupportsInterp(e)
      ensures EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es', env, ctx'))
      decreases es, env, 0
      // Auxiliary lifting lemma for the ``Block`` case
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal SupportsInterp();
      reveal InterpBlock_Exprs();

      var res := InterpBlock_Exprs(es, env, ctx);
      var res' := InterpBlock_Exprs(es', env, ctx');

      if es == [] {
        // Trivial 
      }
      else if |es| == 1 {
        assert es == [es[0]];
        assert es' == [es'[0]];

        var res0 := InterpExpr(es[0], env, ctx);
        var res0' := InterpExpr(es'[0], env, ctx');
        EqInterp_Lem(es[0], es'[0], env, ctx, ctx');
      }
      else {
        // Evaluate the first expression
        var res0 := InterpExpr(es[0], env, ctx);
        var res0' := InterpExpr(es'[0], env, ctx');
        EqInterp_Lem(es[0], es'[0], env, ctx, ctx');

        // Evaluate the remaining expressions
        if res0.Success? && res0.value.ret == V.Unit {
          var Return(_, ctx0) := res0.value;
          var Return(_, ctx0') := res0'.value;
          
          var res1 := InterpBlock_Exprs(es[1..], env, ctx0);
          var res1' := InterpBlock_Exprs(es'[1..], env, ctx0');

          assert res1 == res;
          assert res1' == res';

          EqInterp_Expr_BlockExprs_CanBeMapLifted_Lem(es[1..], es'[1..], env, ctx0, ctx0');
        }
        else {
          // Trivial
        }
      }
    }



    lemma EqInterp_Expr_Block_CanBeMapLifted_Lem(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
      requires e.Block?
      requires e'.Block?
      requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
      ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
      decreases e, env, 0
    {
      reveal EqInterp_CanBeMapLifted_Pre();
      reveal EqInterp_CanBeMapLifted_Post();

      reveal InterpExpr();
      reveal InterpBlock();
      reveal SupportsInterp();

      var es := e.stmts;
      var es' := e'.stmts;
      EqInterp_Expr_BlockExprs_CanBeMapLifted_Lem(es, es', env, ctx, ctx');

      var res := InterpExpr(e, env, ctx);
      var res' := InterpExpr(e', env, ctx');

      // Doesn't work without those assertions, for some reason
      assert res == InterpBlock(es, env, ctx);
      assert res' == InterpBlock(es', env, ctx');
    }

    lemma EqInterp_CanBeMapLifted_Lem()
      ensures RelCanBeMapLifted(EqInterp)
    {
      forall e, e'
        ensures
           (&& Exprs.ConstructorsMatch(e, e')
            && All_Rel_Forall(EqInterp, e.Children(), e'.Children()))
            ==> EqInterp(e, e')
      {
        if && Exprs.ConstructorsMatch(e, e')
           && All_Rel_Forall(EqInterp, e.Children(), e'.Children()) {
          if SupportsInterp(e) {
            reveal SupportsInterp();
            assert SupportsInterp(e');

            forall env, ctx, ctx' | EqState(ctx, ctx') ensures
              EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx')) {
              reveal EqInterp_CanBeMapLifted_Pre();
              reveal EqInterp_CanBeMapLifted_Post();
              EqInterp_Expr_CanBeMapLifted_Lem(e, e', env, ctx, ctx');
            }
          }
          else {}
        }
        else {}
      }
    }
}

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

  predicate {:verify false} MapChildrenPreservesPre(f: Expr --> Expr, post: Expr -> bool)
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

  predicate {:verify false} TransformerMatchesPrePost(f: Expr --> Expr, post: Expr -> bool)
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
  predicate {:verify false} TransformerShallowPreservesRel(f: Expr --> Expr, rel: (Expr, Expr) -> bool)
  // `f` relates its input and its output with `rel`.
  {
    forall e | f.requires(e) :: rel(e, f(e))
  }

  predicate {:verify false} TransformerDeepPreservesRel(f: Expr --> Expr, rel: (Expr, Expr) -> bool)
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

  predicate {:verify false} IsBottomUpTransformer(f: Expr --> Expr, post: Expr -> bool)
  // Predicate for ``BottomUpTransformer``
  {
    && TransformerMatchesPrePost(f, post)
    && MapChildrenPreservesPre(f, post)
  }

  // Identity bottom-up transformer: we need it only because we need a witness when
  // defining ``BottomUpTransformer``, to prove that the type is inhabited.
  const {:verify false} IdentityTransformer: ExprTransformer :=
    TR(d => d, _ => true)

  predicate IdentityTransformerRel(e: Expr, e': Expr)
  {
    true
  }

  lemma {:verify false} IdentityMatchesPrePost()
    ensures TransformerMatchesPrePost(IdentityTransformer.f, IdentityTransformer.post)
  { }

  lemma {:verify false} IdentityPreservesPre()
    ensures MapChildrenPreservesPre(IdentityTransformer.f, IdentityTransformer.post)
  { }

  lemma IdentityPreservesRel()
    ensures TransformerDeepPreservesRel(IdentityTransformer.f, IdentityTransformerRel)
  { }

  // FIXME(CPC): Move to equivs (use a datatype to make this a member function)
  predicate {:verify false} RelCanBeMapLifted(rel: (Expr, Expr) -> bool)
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
  type {:verify false} BottomUpTransformer = tr: ExprTransformer | IsBottomUpTransformer(tr.f, tr.post)
    witness (IdentityMatchesPrePost();
             IdentityPreservesPre();
             IdentityTransformer)

  function method MapChildren_Expr(e: Expr, tr: BottomUpTransformer) :
    (e': Expr)
    decreases e, 0
    requires Deep.AllChildren_Expr(e, tr.f.requires)
    ensures Deep.AllChildren_Expr(e', tr.post)
    ensures Exprs.ConstructorsMatch(e, e')
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
      case VarDecl(vdecls, ovals) =>
        var ovals' :=
          match ovals
            case Some(vals) => Exprs.Some(Seq.Map(e requires e in vals => Map_Expr(e, tr), vals))
            case None => Exprs.None;
        var e' := Expr.VarDecl(vdecls, ovals');
        e'
      case Update(vars, vals) =>
        var vals' := Seq.Map(e requires e in vals => Map_Expr(e, tr), vals);
        var e' := Expr.Update(vars, vals');
        e'
      case If(cond, thn, els) =>
        var e' := Expr.If(Map_Expr(cond, tr), Map_Expr(thn, tr), Map_Expr(els, tr));
        assert Exprs.ConstructorsMatch(e, e');
        e'
    }
  }

  // Apply a transformer bottom-up on an expression.
  function method {:verify false} Map_Expr(e: Expr, tr: BottomUpTransformer) : (e': Expr)
    decreases e, 1
    requires Deep.All_Expr(e, tr.f.requires)
    ensures Deep.All_Expr(e', tr.post)
    // Apply a transformer bottom-up on an expression.
  {
    Deep.AllImpliesChildren(e, tr.f.requires);
    tr.f(MapChildren_Expr(e, tr))
  }

  function method MapChildren_Expr_WithRel(e: Expr, tr: BottomUpTransformer, ghost rel: (Expr, Expr) -> bool) :
    (e': Expr)
    decreases e, 0
    requires Deep.AllChildren_Expr(e, tr.f.requires)
    requires TransformerDeepPreservesRel(tr.f, rel)
    ensures Deep.AllChildren_Expr(e', tr.post)
    ensures Exprs.ConstructorsMatch(e, e')
    ensures All_Rel_Forall(rel, e.Children(), e'.Children())
    ensures e' == MapChildren_Expr(e, tr)
    // Apply a transformer bottom-up on the children of an expression, and prove that it preserves a relation.
  {
    match e {
      case Var(_) => e
      case Literal(lit_) => e
      case Abs(vars, body) => Expr.Abs(vars, Map_Expr_WithRel(body, tr, rel))
      case Apply(aop, exprs) =>
        // BUG(https://github.com/dafny-lang/dafny/issues/2435): we can't apply `Map_Expr_WithRel`
        // through `Seq.Map` because then the compiled code is incorrect.
        // For this reason we apply `Map_Expr` instead of `Map_Expr_WithRel` and leverage the fact
        // that those two functions return the same output.
        var exprs' := Seq.Map(e requires e in exprs => Map_Expr(e, tr), exprs);
        Map_All_IsMap(e requires e in exprs => Map_Expr(e, tr), exprs);
        Map_All_IsMap(e requires e in exprs => Map_Expr_WithRel(e, tr, rel), exprs);
        var e' := Expr.Apply(aop, exprs');
        assert Exprs.ConstructorsMatch(e, e');
        e'
      case Block(exprs) =>
        var exprs' := Seq.Map(e requires e in exprs => Map_Expr_WithRel(e, tr, rel), exprs);
        Map_All_IsMap(e requires e in exprs => Map_Expr_WithRel(e, tr, rel), exprs);
        var e' := Expr.Block(exprs');
        assert Exprs.ConstructorsMatch(e, e');
        e'
      case VarDecl(vdecls, ovals) =>
        var ovals' :=
          match ovals {
            case Some(vals) =>
              Map_All_IsMap(e requires e in vals => Map_Expr_WithRel(e, tr, rel), vals);
              Exprs.Some(Seq.Map(e requires e in vals => Map_Expr_WithRel(e, tr, rel), vals))
            case None => Exprs.None
          };
        var e' := Expr.VarDecl(vdecls, ovals');
        e'
      case Update(vars, vals) =>
        var vals' := Seq.Map(e requires e in vals => Map_Expr_WithRel(e, tr, rel), vals);
        Map_All_IsMap(e requires e in vals => Map_Expr_WithRel(e, tr, rel), vals);
        var e' := Expr.Update(vars, vals');
        e'
      case If(cond, thn, els) =>
        var e' := Expr.If(Map_Expr_WithRel(cond, tr, rel), Map_Expr_WithRel(thn, tr, rel), Map_Expr_WithRel(els, tr, rel));
        assert Exprs.ConstructorsMatch(e, e');
        e'
    }
  }

  function method Map_Expr_WithRel(e: Expr, tr: BottomUpTransformer, ghost rel: (Expr, Expr) -> bool) : (e': Expr)
    decreases e, 1
    requires Deep.All_Expr(e, tr.f.requires)
    requires TransformerDeepPreservesRel(tr.f, rel)
    ensures Deep.All_Expr(e', tr.post)
    ensures rel(e, e')
    ensures e' == Map_Expr(e, tr)
    // Apply a transformer bottom-up on an expression, and prove that it preserves a relation.
  {
    Deep.AllImpliesChildren(e, tr.f.requires);
    tr.f(MapChildren_Expr_WithRel(e, tr, rel))
  }


  lemma MapChildren_Expr_PreservesRel(e: Expr, tr: BottomUpTransformer, rel: (Expr, Expr) -> bool)
    requires Deep.AllChildren_Expr(e, tr.f.requires)
    requires TransformerDeepPreservesRel(tr.f, rel)
    ensures All_Rel_Forall(rel, e.Children(), MapChildren_Expr(e, tr).Children())
    // If `rel` preserves a relation, ``MapChildren_Expr`` preserves the same relation.
  {
    var _ := MapChildren_Expr_WithRel(e, tr, rel);
  }

  lemma Map_Expr_PreservesRel(e: Expr, tr: BottomUpTransformer, rel: (Expr, Expr) -> bool)
    decreases e, 1
    requires Deep.All_Expr(e, tr.f.requires)
    requires TransformerDeepPreservesRel(tr.f, rel)
    ensures rel(e, Map_Expr(e, tr))
    // If `rel` preserves a relation, ``Map_Expr`` preserves the same relation.
  {
    var _ := Map_Expr_WithRel(e, tr, rel);
  }

  function method Map_Expr_Transformer(tr: BottomUpTransformer) :
    (tr': ExprTransformer)
    // Given a bottom-up transformer `tr`, return a transformer which applies `tr` in
    // a bottom-up manner.
  {
    TR(e requires Deep.All_Expr(e, tr.f.requires) => Map_Expr(e, tr),
       e' => Deep.All_Expr(e', tr.post))
  }

  lemma Map_Expr_Transformer_PreservesRel(tr: BottomUpTransformer, rel: (Expr, Expr) -> bool)
    requires TransformerDeepPreservesRel(tr.f, rel)
    ensures Map_Expr_Transformer(tr).HasValidRel(rel)
  {
    var tr' := Map_Expr_Transformer(tr);
    forall e:Expr
      ensures tr'.f.requires(e) ==> rel(e, tr'.f(e))
    {
      if tr'.f.requires(e) {
        var e2 := tr'.f(e);
        Map_Expr_PreservesRel(e, tr, rel);
        match e {
          case Var(_) => {}
          case Literal(_) => {}
          case Abs(vars, body) =>
            assert rel(e, tr'.f(e));
          case Apply(applyOp, args) =>
            assert rel(e, tr'.f(e));
          case Block(stmts) =>
            assert rel(e, tr'.f(e));
          case VarDecl(vdecls, ovals) =>
            assert rel(e, tr'.f(e));
          case Update(vars, vals) =>
            assert rel(e, tr'.f(e));
          case If(cond, thn, els) => {
            assert rel(e, tr'.f(e));
          }
        }
      }
    }
  }

  function method {:verify false} {:opaque} Map_Method(m: Method, tr: BottomUpTransformer) :
    (m': Method)
    requires Deep.All_Method(m, tr.f.requires)
    ensures Deep.All_Method(m', tr.post)
    // Apply a transformer to a method, in a bottom-up manner.
  {
    Shallow.Map_Method(m, Map_Expr_Transformer(tr))
  }

  function method {:verify false} {:opaque} Map_Program(p: Program, tr: BottomUpTransformer) :
    (p': Program)
    requires Deep.All_Program(p, tr.f.requires)
    ensures Deep.All_Program(p', tr.post)
    // Apply a transformer to a program, in a bottom-up manner.
  {
    Shallow.Map_Program(p, Map_Expr_Transformer(tr))
  }

  lemma {:opaque} Map_Method_PreservesRel(m: Method, tr: BottomUpTransformer, rel: (Expr, Expr) -> bool)
    requires Deep.All_Method(m, tr.f.requires)
    requires TransformerDeepPreservesRel(tr.f, rel)
    ensures rel(m.methodBody, Map_Method(m, tr).methodBody)
    // ``Map_Method`` preserves relations
  {
    reveal Map_Method();
    reveal Shallow.Map_Method();
    Map_Expr_PreservesRel(m.methodBody, tr, rel);
  }

  lemma {:opaque} Map_Program_PreservesRel(p: Program, tr: BottomUpTransformer, rel: (Expr, Expr) -> bool)
    requires Deep.All_Program(p, tr.f.requires)
    requires TransformerDeepPreservesRel(tr.f, rel)
    ensures rel(p.mainMethod.methodBody, Map_Program(p, tr).mainMethod.methodBody)
    // ``Map_Program`` preserves relations
  {
    reveal Map_Method();
    reveal Map_Program();
    reveal Shallow.Map_Method();
    reveal Shallow.Map_Program();
    Map_Method_PreservesRel(p.mainMethod, tr, rel);
  }

  lemma TransformationAndRel_Lift(f: Expr --> Expr, rel: (Expr, Expr) -> bool)
    requires RelIsTransitive(rel)
    requires RelCanBeMapLifted(rel)
    requires TransformerShallowPreservesRel(f, rel)
    ensures TransformerDeepPreservesRel(f, rel)
    // Lifting lemma for a relation like ``EqInterp``: under some conditions on
    // the relation, it is possible to simply prove that `f` links its input
    // and output with `rel` to be able to lift it through map.
  {}
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


  type {:verify false} Expr = Syntax.Expr
  type {:verify false} WV = Interp.Value // FIXME
  type {:verify false} EqWV = Interp.EqWV // FIXME
  type {:verify false} Context = Values.Context

  // TODO: maybe not necessary to make this opaque
  // FIXME(CPC): Change to Interp.Expr and remove SupportsInterp below
  predicate {:verify false} {:opaque} EqInterp_CanBeMapLifted_Pre(e: Expr, e': Expr, env: Environment, ctx: State, ctx': State)
  {
    && EqState(ctx, ctx')
    && Exprs.ConstructorsMatch(e, e')
    && All_Rel_Forall(EqInterp, e.Children(), e'.Children())
    && SupportsInterp(e) // TODO: remove (`Expr` is now a subset type)
    && SupportsInterp(e') // TODO: remove (`Expr` is now a subset type)
    && InterpExpr(e, env, ctx).Success? // We eliminate the failure case, which is trivial
  }

  // TODO: maybe not necessary to make this opaque
  predicate {:verify false} {:opaque} EqInterp_CanBeMapLifted_Post(e: Expr, e': Expr, env: Environment, ctx: State, ctx': State)
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
  {
    reveal EqInterp_CanBeMapLifted_Pre();
    EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
  }

  lemma {:verify false} EqInterp_Expr_CanBeMapLifted(e: Expr, e': Expr, env: Environment, ctx: State, ctx': State)
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 1
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
        EqInterp_Expr_Var_CanBeMapLifted(e, e', env, ctx, ctx');
      }
      case Literal(_) => {
        EqInterp_Expr_Literal_CanBeMapLifted(e, e', env, ctx, ctx');
      }
      case Abs(_, _) => {
        EqInterp_Expr_Abs_CanBeMapLifted(e, e', env, ctx, ctx');
      }
      case Apply(Lazy(_), _) => {
        EqInterp_Expr_ApplyLazy_CanBeMapLifted(e, e', env, ctx, ctx');
      }
      case Apply(Eager(_), _) => {
        EqInterp_Expr_ApplyEager_CanBeMapLifted(e, e', env, ctx, ctx');
      }
      case If(_, _, _) => {
        EqInterp_Expr_If_CanBeMapLifted(e, e', env, ctx, ctx');
      }
      case VarDecl(_, _) => {
        EqInterp_Expr_VarDecl_CanBeMapLifted(e, e', env, ctx, ctx');
      }
      case Update(_, _) => {
        EqInterp_Expr_Update_CanBeMapLifted(e, e', env, ctx, ctx');
      }
      case Block(_) => {
        EqInterp_Expr_Block_CanBeMapLifted(e, e', env, ctx, ctx');
      }
      case _ => {
        // Unsupported branch
        reveal SupportsInterp(); // We need this to see that some variants are not supported
        assert false;
      }
    }
  }

  lemma {:verify false} EqInterp_Expr_Var_CanBeMapLifted(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
    requires e.Var?
    requires e'.Var?
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 0
  {
    reveal EqInterp_CanBeMapLifted_Pre();
    reveal EqInterp_CanBeMapLifted_Post();

    reveal InterpExpr();
    reveal GEqCtx();

    var v := e.name;
    assert v == e'.name;
    
    var res := InterpVar(v, ctx', env);
    var res' := InterpVar(v, ctx', env);

    // Start by looking in the local context
    var res0 := TryGetVariable(ctx.locals, v, UnboundVariable(v));
    var res0' := TryGetVariable(ctx'.locals, v, UnboundVariable(v));

    if res0.Success? {
      assert res0.Success?;
    }
    else {
      // Not in the local context: look in the global context
      if v in env.globals {
        EqValue_Refl(env.globals[v]);
      }
    }
  }

  // FIXME(CPC): Can this lemma and the following ones use Interp.Expr?
  lemma {:verify false} EqInterp_Expr_Literal_CanBeMapLifted(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
    requires e.Literal?
    requires e'.Literal?
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 0
  {
    reveal EqInterp_CanBeMapLifted_Pre();
    reveal EqInterp_CanBeMapLifted_Post();

    reveal InterpExpr();
    reveal InterpLiteral();
  }

  lemma EqInterp_Expr_Abs_CanBeMapLifted(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
    requires e.Abs?
    requires e'.Abs?
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 0
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
      EqInterp_Expr_AbsClosure_CanBeMapLifted(cv, cv', env, argvs, argvs');
    }

    assert EqValue_Closure(cv, cv') by {
      reveal EqValue_Closure();
    }
  }

  lemma {:verify false} EqInterp_Expr_AbsClosure_CanBeMapLifted(cv: WV, cv': WV, env: Environment, argvs: seq<WV>, argvs': seq<WV>)
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
    BuildCallState_EqState(cv.ctx, cv'.ctx, cv.vars, argvs, argvs');
    assert EqState(ctx1, ctx1');

    assert EqPureInterpResultValue(res, res') by {
      reveal InterpCallFunctionBody();
    }
  }

  lemma {:verify false} EqInterp_Expr_ApplyLazy_CanBeMapLifted(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
    requires e.Apply? && e.aop.Lazy?
    requires e'.Apply? && e'.aop.Lazy?
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 0
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
    EqInterp_Inst(e0, e0', env, ctx, ctx');
    var ret0 :- assert InterpExprWithType(e0, Type.Bool, env, ctx);
    var ret0' :- assert InterpExprWithType(e0', Type.Bool, env, ctx');
    var Return(v0, ctx0) := ret0;
    var Return(v0', ctx0') := ret0';

    EqInterp_Inst(e1, e1', env, ctx0, ctx0');
    // The proof fails if we don't introduce res1 and res1'
    var res1 := InterpExprWithType(e1, Type.Bool, env, ctx0);
    var res1' := InterpExprWithType(e1', Type.Bool, env, ctx0');
  }

  lemma {:verify false} EqInterp_Expr_ApplyEager_CanBeMapLifted(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
    requires e.Apply? && e.aop.Eager?
    requires e'.Apply? && e'.aop.Eager?
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 0
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
    InterpExprs_EqInterp_Inst(args, args', env, ctx, ctx');
    var ret0 :- assert InterpExprs(args, env, ctx);
    var ret0' :- assert InterpExprs(args', env, ctx');

    var Return(argvs, ctx0) := ret0;
    var Return(argvs', ctx0') := ret0';

    match (op, op') {
      case (UnaryOp(op), UnaryOp(op')) => {
        assert op == op';
        EqInterp_Expr_UnaryOp_CanBeMapLifted(e, e', op, argvs[0], argvs'[0]);
        assert EqInterpResultValue(res, res');
      }
      case (BinaryOp(bop), BinaryOp(bop')) => {
        assert bop == bop';
        EqInterp_Expr_BinaryOp_CanBeMapLifted(e, e', bop, argvs[0], argvs[1], argvs'[0], argvs'[1]);
        assert EqInterpResultValue(res, res');
      }
      case (TernaryOp(top), TernaryOp(top')) => {
        assert top == top';
        EqInterp_Expr_TernaryOp_CanBeMapLifted(e, e', top, argvs[0], argvs[1], argvs[2], argvs'[0], argvs'[1], argvs'[2]);
        assert EqInterpResultValue(res, res');
      }
      case (Builtin(Display(ty)), Builtin(Display(ty'))) => {
        assert ty == ty';
        EqInterp_Expr_Display_CanBeMapLifted(e, e', ty.kind, argvs, argvs');
        assert EqInterpResultValue(res, res');
      }
      case (FunctionCall(), FunctionCall()) => {
        EqInterp_Expr_FunctionCall_CanBeMapLifted(e, e', env, argvs[0], argvs'[0], argvs[1..], argvs'[1..]);
        assert EqInterpResultValue(res, res');
      }
      case _ =>
    }
  }

  // TODO: e and e' should be the same actually
  lemma {:verify false} EqInterp_Expr_UnaryOp_CanBeMapLifted(
    e: Interp.Expr, e': Interp.Expr, op: UnaryOp, v: WV, v': WV
  )
    requires !op.MemberSelect?
    requires EqValue(v, v')
    requires InterpUnaryOp(e, op, v).Success?
    ensures EqPureInterpResultValue(InterpUnaryOp(e, op, v), InterpUnaryOp(e', op, v'))
  {
    reveal InterpUnaryOp();

    var ret :- assert InterpUnaryOp(e, op, v);
    var ret' :- assert InterpUnaryOp(e', op, v');

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

  // TODO: we could split this lemma, whose proof is big (though straightforward),
  // but it is a bit annoying to do...
  lemma EqInterp_Expr_BinaryOp_CanBeMapLifted(
    e: Interp.Expr, e': Interp.Expr, bop: BinaryOp, v0: WV, v1: WV, v0': WV, v1': WV
  )
    requires !bop.BV? && !bop.Datatypes?
    requires EqValue(v0, v0')
    requires EqValue(v1, v1')
    requires InterpBinaryOp(e, bop, v0, v1).Success?
    ensures EqPureInterpResultValue(InterpBinaryOp(e, bop, v0, v1), InterpBinaryOp(e', bop, v0', v1'))
  {
    InterpBinaryOp_Eq(e, e', bop, v0, v1, v0', v1');
  }

  lemma EqInterp_Expr_TernaryOp_CanBeMapLifted(
    e: Interp.Expr, e': Interp.Expr, top: TernaryOp, v0: WV, v1: WV, v2: WV, v0': WV, v1': WV, v2': WV
  )
    requires EqValue(v0, v0')
    requires EqValue(v1, v1')
    requires EqValue(v2, v2')
    requires InterpTernaryOp(e, top, v0, v1, v2).Success?
    ensures EqPureInterpResultValue(InterpTernaryOp(e, top, v0, v1, v2), InterpTernaryOp(e', top, v0', v1', v2'))
  {
    // TODO: using this lemma makes Dafny crash...
    // InterpTernaryOp_Eq(e, e', top, v0, v1, v2, v0', v1', v2');

    reveal InterpTernaryOp();

    var res := InterpTernaryOp(e, top, v0, v1, v2);
    var res' := InterpTernaryOp(e', top, v0', v1', v2');

    match top {
      case Sequences(op) => {}
      case Multisets(op) => {
        EqValue_HasEqValue_Eq(v1, v1');
      }
      case Maps(op) => {
        EqValue_HasEqValue_Eq(v1, v1');
      }
    }
  }

  lemma {:verify false} EqInterp_Expr_Display_CanBeMapLifted(
    e: Interp.Expr, e': Interp.Expr, kind: Types.CollectionKind, vs: seq<WV>, vs': seq<WV>
  )
    requires EqSeqValue(vs, vs')
    requires InterpDisplay(e, kind, vs).Success?
    ensures EqPureInterpResultValue(InterpDisplay(e, kind, vs), InterpDisplay(e', kind, vs'))
  {
    reveal InterpDisplay();

    var res := InterpDisplay(e, kind, vs);
    var res' := InterpDisplay(e', kind, vs');

    match kind {
      case Map(_) => {
        InterpMapDisplay_EqArgs(e, e', vs, vs');
        assert EqPureInterpResultValue(res, res');
      }
      case Multiset => {
        EqValue_HasEqValue_Eq_Forall();
        assert (forall i | 0 <= i < |vs| :: HasEqValue(vs[i]));
        assert (forall i | 0 <= i < |vs| :: HasEqValue(vs'[i]));
        assert (forall i | 0 <= i < |vs| :: EqValue(vs[i], vs'[i]));
        assert vs == vs';
        assert EqPureInterpResultValue(res, res');
      }
      case Seq => {
        assert EqPureInterpResultValue(res, res');
      }
      case Set => {
        EqValue_HasEqValue_Eq_Forall();
        assert EqPureInterpResultValue(res, res');
      }
    }
  }

  lemma EqInterp_Expr_FunctionCall_CanBeMapLifted(
    e: Interp.Expr, e': Interp.Expr, env: Environment, f: WV, f': WV, argvs: seq<WV>, argvs': seq<WV>
  )
    requires EqValue(f, f')
    requires EqSeqValue(argvs, argvs')
    requires InterpFunctionCall(e, env, f, argvs).Success?
    ensures EqPureInterpResultValue(InterpFunctionCall(e, env, f, argvs),
                                    InterpFunctionCall(e', env, f', argvs'))
  {
    InterpFunctionCall_EqState(e, e', env, f, f', argvs, argvs');
  }

  lemma {:verify false} EqInterp_Expr_If_CanBeMapLifted(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
    requires e.If?
    requires e'.If?
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 0
  {
    reveal EqInterp_CanBeMapLifted_Pre();
    reveal EqInterp_CanBeMapLifted_Post();

    reveal InterpExpr();
    reveal SupportsInterp();

    var res := InterpExpr(e, env, ctx);
    var res' := InterpExpr(e', env, ctx');

    var If(cond, thn, els) := e;
    var If(cond', thn', els') := e';

    // Of course, proof fails without those (forall quantifier instantiation)...
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

    EqInterp_Inst(cond, cond', env, ctx, ctx');
    assert EqInterpResultValue(res0, res0');

    var Return(condv, ctx0) := res0.value;
    var Return(condv', ctx0') := res0'.value;

    EqInterp_Inst(thn, thn', env, ctx0, ctx0'); // Proof fails without this
    EqInterp_Inst(els, els', env, ctx0, ctx0'); // Proof fails without this
  }

  // We can't use the type `seq<Interp.Expr>` for `es` and `es'`, because then Dafny is unable to
  // prove the requires clauses.
  lemma EqInterp_Expr_BlockExprs_CanBeMapLifted(es: seq<Exprs.T>, es': seq<Exprs.T>, env: Environment, ctx: State, ctx': State)
    requires EqState(ctx, ctx')
    requires All_Rel_Forall(EqInterp, es, es')
    requires forall e | e in es :: SupportsInterp(e)
    requires forall e | e in es' :: SupportsInterp(e)
    requires InterpBlock_Exprs(es, env, ctx).Success?
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
      EqInterp_Inst(es[0], es'[0], env, ctx, ctx');
    }
    else {
      // Evaluate the first expression
      var res0 := InterpExprWithType(es[0], Types.Unit, env, ctx);
      var res0' := InterpExprWithType(es'[0], Types.Unit, env, ctx');
      EqInterp_Inst(es[0], es'[0], env, ctx, ctx');

      // Evaluate the remaining expressions
      var Return(_, ctx0) := res0.value;
      var Return(_, ctx0') := res0'.value;

      var res1 := InterpBlock_Exprs(es[1..], env, ctx0);
      var res1' := InterpBlock_Exprs(es'[1..], env, ctx0');

      assert res1 == res;
      assert res1' == res';

      EqInterp_Expr_BlockExprs_CanBeMapLifted(es[1..], es'[1..], env, ctx0, ctx0');
    }
  }

  lemma EqInterp_Expr_Block_CanBeMapLifted(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
    requires e.Block?
    requires e'.Block?
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 0
  {
    reveal EqInterp_CanBeMapLifted_Pre();
    reveal EqInterp_CanBeMapLifted_Post();

    reveal InterpExpr();
    reveal InterpBlock();
    reveal SupportsInterp();

    var res := InterpExpr(e, env, ctx);
    var res' := InterpExpr(e', env, ctx');

    var ctx1 := ctx.(rollback := map []);
    var ctx1' := ctx'.(rollback := map []);

    assert EqState(ctx1, ctx1') by { reveal GEqCtx(); }

    var es := e.stmts;
    var es' := e'.stmts;
    // Doesn't work without those assertions, for some reason (probably a problem of fuel)
    assert res == InterpBlock(es, env, ctx);
    assert res' == InterpBlock(es', env, ctx');

    var res0 := InterpBlock_Exprs(es, env, ctx1);
    var res0' := InterpBlock_Exprs(es', env, ctx1');
    EqInterp_Expr_BlockExprs_CanBeMapLifted(es, es', env, ctx1, ctx1');
    assert EqInterpResultValue(res0, res0');
    
    reveal GEqCtx();
  }
  
  lemma EqInterp_Expr_VarDecl_CanBeMapLifted(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
    requires e.VarDecl?
    requires e'.VarDecl?
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 0
  {
    reveal EqInterp_CanBeMapLifted_Pre();
    reveal EqInterp_CanBeMapLifted_Post();
    reveal InterpExpr();

    var VarDecl(vdecls, ovals) := e;
    var VarDecl(vdecls', ovals') := e';

    var res := InterpExpr(e, env, ctx);
    var res' := InterpExpr(e', env, ctx');

    var vars := Seq.Map((v: Exprs.Var) => v.name, vdecls);

    assert vdecls == vdecls';

    if ovals.Some? {
      reveal SupportsInterp();
      var res0 := InterpExprs(ovals.value, env, ctx);
      var res0' := InterpExprs(ovals'.value, env, ctx');

      InterpExprs_EqInterp_Inst(ovals.value, ovals'.value, env, ctx, ctx');
      assert EqInterpResult(EqSeqValue, res0, res0');

      var Return(vals, ctx0) := res0.value;
      var Return(vals', ctx0') := res0'.value;

      var ctx1 := SaveToRollback(ctx0, vars);
      var ctx1' := SaveToRollback(ctx0', vars);
      SaveToRollback_Equiv(ctx0, ctx0', vars);
      assert EqState(ctx1, ctx1');

      var ctx2 := ctx1.(locals := AugmentContext(ctx1.locals, vars, vals));
      var ctx2' := ctx1'.(locals := AugmentContext(ctx1'.locals, vars, vals'));
      AugmentContext_Equiv(ctx1.locals, ctx1'.locals, vars, vals, vals');
      assert EqState(ctx2, ctx2');

      assert res == Success(Return(Unit, ctx2)) by { reveal InterpExpr(); }
      assert res' == Success(Return(Unit, ctx2')) by { reveal InterpExpr(); }
    }
    else {
      SaveToRollback_Equiv(ctx, ctx', vars);
      var ctx1 := SaveToRollback(ctx, vars);
      var ctx1' := SaveToRollback(ctx', vars);
      assert EqState(ctx1, ctx1');
    }
  }

  lemma EqInterp_Expr_Update_CanBeMapLifted(e: Interp.Expr, e': Interp.Expr, env: Environment, ctx: State, ctx': State)
    requires e.Update?
    requires e'.Update?
    requires EqInterp_CanBeMapLifted_Pre(e, e', env, ctx, ctx')
    ensures EqInterp_CanBeMapLifted_Post(e, e', env, ctx, ctx')
    decreases e, 0
  {      
    reveal EqInterp_CanBeMapLifted_Pre();
    reveal EqInterp_CanBeMapLifted_Post();

    reveal InterpExpr();
    reveal SupportsInterp();

    var res := InterpExpr(e, env, ctx);
    var res' := InterpExpr(e', env, ctx');

    var Update(vars, vals) := e;
    var Update(vars', vals') := e';
    assert vars' == vars;

    // The rhs evaluate to similar results
    var res0 := InterpExprs(vals, env, ctx);
    var res0' := InterpExprs(vals', env, ctx');
    InterpExprs_EqInterp_Inst(vals, vals', env, ctx, ctx');
    assert EqInterpResult(EqSeqValue, res0, res0');

    // Dafny crashes if we try to deconstruct the `Return`s in the match.
    // See: https://github.com/dafny-lang/dafny/issues/2258
    var Return(valsvs, ctx0) := res0.value;
    var Return(valsvs', ctx0') := res0'.value;

    AugmentContext_Equiv(ctx0.locals, ctx0'.locals, vars, valsvs, valsvs');
    var ctx1 := ctx0.(locals := AugmentContext(ctx0.locals, vars, valsvs));
    var ctx1' := ctx0'.(locals := AugmentContext(ctx0'.locals, vars, valsvs'));
    assert EqState(ctx1, ctx1');

    assert res == Success(Return(Unit, ctx1));
    assert res' == Success(Return(Unit, ctx1'));
  }

  lemma EqInterp_CanBeMapLifted()
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
            if InterpExpr(e, env, ctx).Success? {
              EqInterp_Expr_CanBeMapLifted(e, e', env, ctx, ctx');
            }
            else {
              // Trivial
            }
          }
        }
        else {}
      }
      else {}
    }
  }

  // TODO(SMH): move? (or even remove?)
  lemma EqInterp_CanBeComposed(f: Expr --> Expr, g: Expr --> Expr)
    requires TransformerShallowPreservesRel(f, EqInterp)
    requires TransformerShallowPreservesRel(g, EqInterp)
    requires forall x | f.requires(x) :: g.requires(f(x))
    ensures TransformerShallowPreservesRel(Comp(f, g), EqInterp)
  {
    forall e | f.requires(e) ensures EqInterp(e, g(f(e)))
    {
      assert EqInterp(e, f(e));
      assert EqInterp(f(e), g(f(e)));
      EqInterp_Trans(e, f(e), g(f(e)));
    }
  }

  lemma EqInterp_Lift(f: Expr --> Expr)
    requires TransformerShallowPreservesRel(f, EqInterp)
    ensures TransformerDeepPreservesRel(f, EqInterp)
    // It is enough to prove that `f` links its input and output with ``EqInterp``
    // to be able to lift it through map.
  {
     EqInterp_IsTransitive();
     EqInterp_CanBeMapLifted();
     TransformationAndRel_Lift(f, EqInterp); 
  }
}

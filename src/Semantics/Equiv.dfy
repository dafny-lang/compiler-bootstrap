include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Interop/CSharpDafnyASTInterop.dfy"
include "../Utils/Library.dfy"
include "Interp.dfy"
include "../Transforms/Generic.dfy"
include "../Transforms/Shallow.dfy"

module Bootstrap.Semantics.Equiv {
  // This module introduces the relations we use to describe values and expressions
  // as equivalent, and which we use to state that our compilation passes are sound.
  //
  // TODO(SMH): use ``Expr`` instead of ``Exprs.T`` and remove the requirements about ``SupportsInterp``?

  import Utils.Lib
  import Utils.Lib.Debug
  import opened AST.Syntax
  import opened Utils.Lib.Datatypes

  import opened AST.Predicates
  import opened Interp
  import opened Values

  type Expr = Syntax.Expr
  type WV = Interp.Value // FIXME
  type EqWV = Interp.EqWV // FIXME
  type Context = Values.Context

  // TODO(SMH): move
  predicate Seq_All<T>(f: T -> bool, s: seq<T>)
  {
    forall x | x in s :: f(x)
  }

  // We introduce ``Equivs`` because in some situations we want to make ``EqValue``
  // and ``EqState`` opaque, and we can't (at least ``EqValue`` - see the comments for
  // this definition).
  // TODO: We should use ``Equivs`` in a more systematic manner, or remove it. If we
  // want to use it more, it would be good to turn some of the functions below to member
  // methods.
  datatype Equivs =
    EQ(eq_value: (WV, WV) -> bool, eq_state: (State, State) -> bool)

  // TODO: not sure it was worth making this opaque
  predicate {:opaque} GEqCtx(
    eq_value: (WV,WV) -> bool, ctx: Context, ctx': Context
  )
    requires WellFormedContext(ctx)
    requires WellFormedContext(ctx')
  {
    && ctx.Keys == ctx'.Keys
    && (forall x | x in ctx.Keys :: eq_value(ctx[x], ctx'[x]))
  }

  predicate GEqState(
    eq_value: (WV,WV) -> bool, ctx: State, ctx': State)
  {
    GEqCtx(eq_value, ctx.locals, ctx'.locals)
  }

  function Mk_EqState(eq_value: (WV,WV) -> bool): (State,State) -> bool
  {
    (ctx, ctx') => GEqState(eq_value, ctx, ctx')
  }

  predicate GEqInterpResult<T(0)>(
    eq_ctx: (State,State) -> bool, eq_value: (T,T) -> bool, res: InterpResult<T>, res': InterpResult<T>)
    // Interpretation results are equivalent.
    // "G" stands for "generic".
    // TODO(SMH): be a bit more precise in the error case, especially in case of "out of fuel".
  {
    match (res, res') {
      case (Success(Return(v,ctx)), Success(Return(v',ctx'))) =>
        && eq_ctx(ctx, ctx')
        && eq_value(v, v')
      case (Failure(_), Failure(_)) =>
        true
      case _ =>
        false
    }
  }

  function method {:opaque} InterpCallFunctionBody(fn: WV, env: Environment, argvs: seq<WV>)
    : (r: PureInterpResult<WV>)
    requires fn.Closure?
    requires |fn.vars| == |argvs|
    // Small utility, very similar to ``InterpFunctionCall``, which we use to factorize
    // the definitions. The opaque attribute is maybe not necessary anymore, but as the
    // proofs work with it, we might as well keep it (it is easier to remove an opaque
    // attribute, than to add one and fix the proofs by adding the proper calls to ``reveal``).
  {
    var ctx := BuildCallState(fn.ctx, fn.vars, argvs);
    var Return(val, ctx) :- InterpExpr(fn.body, env, ctx);
    Success(val)
  }

  predicate EqValue(v: WV, v': WV)
    decreases ValueTypeHeight(v) + ValueTypeHeight(v'), 1
    // Equivalence between values.
    //
    // Two values are equivalent if:
    // - they are not closures and are equal/have equivalent children values
    // - they are closures and, when applied to equivalent inputs, they return equivalent outputs
    //
    // Rk.: we could write the predicate in a simpler manner by using `==` in case the values are not
    // closures, but we prepare the terrain for a more general handling of collections.
    //
    // Rk.: for now, we assume the termination. This function terminates because the size of the
    // type of the values decreases, the interesting case being the closures (see ``EqValue_Closure``).
    // Whenever we find a closure `fn_ty = (ty_0, ..., ty_n) -> ret_ty`, we need to call ``EqValue``
    // on valid inputs (with types `ty_i < fn_ty`) and on its output (with type `ret_ty < fn_ty`).
    //
    // Rk.: I initially wanted to make the definition opaque to prevent context saturation, because
    // in most situations we don't need to know the content of EqValue.
    // However it made me run into the following issue:
    // BUG(https://github.com/dafny-lang/dafny/issues/2260)
    // As ``EqValue`` appears a lot in foralls, using the `reveal` trick seemed too cumbersome
    // to be a valid option.
  {
    match (v, v') {
      case (Unit, Unit) => true
      case (Bool(b), Bool(b')) => b == b'
      case (Char(c), Char(c')) => c == c'
      case (Int(i), Int(i')) => i == i'
      case (Real(r), Real(r')) => r == r'
      case (BigOrdinal(o), BigOrdinal(o')) => o == o'
      case (BitVector(width, value), BitVector(width', value')) =>
        && width == width'
        && value == value'
      case (Map(m), Map(m')) =>
        ValueTypeHeight_Children_Lem(v); // For termination
        ValueTypeHeight_Children_Lem(v'); // For termination
        && m.Keys == m'.Keys
        && |m| == |m'| // We *do* need this
        && (forall x | x in m :: EqValue(m[x], m'[x]))
      case (Multiset(ms), Multiset(ms')) =>
        ms == ms'
      case (Seq(sq), Seq(sq')) =>
        ValueTypeHeight_Children_Lem(v); // For termination
        ValueTypeHeight_Children_Lem(v'); // For termination
        && |sq| == |sq'|
        && (forall i | 0 <= i < |sq| :: EqValue(sq[i], sq'[i]))
      case (Set(st), Set(st')) =>
        && st == st'
      case (Closure(ctx, vars, body), Closure(ctx', vars', body')) =>
        EqValue_Closure(v, v')

      // DISCUSS: Better way to write this?  Need exhaustivity checking
      case (Unit, _) => false
      case (Bool(b), _) => false
      case (Char(c), _) => false
      case (Int(i), _) => false
      case (Real(r), _) => false
      case (BigOrdinal(o), _) => false
      case (BitVector(width, value), _) => false
      case (Map(m), _) => false
      case (Multiset(ms), _) => false
      case (Seq(sq), _) => false
      case (Set(st), _) => false
      case (Closure(ctx, vars, body), _) => false
    }
  }

  predicate {:opaque} EqValue_Closure(v: WV, v': WV)
    requires v.Closure?
    requires v'.Closure?
    decreases ValueTypeHeight(v) + ValueTypeHeight(v'), 0
    // Equivalence between values: closure case.
    //
    // See ``EqValue``.
    //
    // Rk.: contrary to ``EqValue``, it seems ok to make ``EqValue_Closure`` opaque.
  {
    var Closure(ctx, vars, body) := v;
    var Closure(ctx', vars', body') := v';
    && |vars| == |vars'|
    && (
    forall env: Environment, argvs: seq<WV>, argvs': seq<WV> |
      && |argvs| == |argvs'| == |vars| // no partial applications are allowed in Dafny
      // We need the argument types to be smaller than the closure types, to prove termination.\
      // In effect, the arguments types should be given by the closure's input types.
      && (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs[i]) < ValueTypeHeight(v))
      && (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs'[i]) < ValueTypeHeight(v'))
      && (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i])) ::
      var res := InterpCallFunctionBody(v, env, argvs);
      var res' := InterpCallFunctionBody(v', env, argvs');
      // We can't use naked functions in recursive setting: this forces us to write the expanded
      // match rather than using an auxiliary function like `EqPureInterpResult`.
      match (res, res') {
        case (Success(ov), Success(ov')) =>
          // We need to assume those assertions to prove termination: the value returned by a closure
          // has a type which is smaller than the closure type (its type is given by the closure return
          // type)
          assume ValueTypeHeight(ov) < ValueTypeHeight(v);
          assume ValueTypeHeight(ov') < ValueTypeHeight(v');
          EqValue(ov, ov')
        case (Failure(_), Failure(_)) =>
          true
        case _ =>
          false
      }
    )
  }

  predicate EqState(ctx: State, ctx': State)
  {
    GEqState(EqValue, ctx, ctx')
  }

  predicate EqCtx(ctx: Context, ctx': Context)
    requires WellFormedContext(ctx)
    requires WellFormedContext(ctx')
  {
    GEqCtx(EqValue, ctx, ctx')
  }

  predicate EqInterpResult<T(0)>(
    eq_value: (T,T) -> bool, res: InterpResult<T>, res': InterpResult<T>)
  {
    GEqInterpResult(Mk_EqState(EqValue), eq_value, res, res')
  }

  lemma EqValueHasEq(v: WV, v': WV)
    requires EqValue(v,v')
    requires HasEqValue(v)
    requires HasEqValue(v')
    ensures v == v'
    // If values are equivalent and have a decidable equality, they are necessarily equal.
  {
    reveal EqValue_Closure();
  }

  lemma EqValueHasEq_Forall()
    ensures forall v: WV, v': WV | EqValue(v,v') && HasEqValue(v) && HasEqValue(v') :: v == v'
  {
    forall v: WV, v': WV | EqValue(v,v') && HasEqValue(v) && HasEqValue(v') ensures v == v' {
      EqValueHasEq(v, v');
    }
  }

  lemma EqInterp_Expr_EqState(e: Exprs.T, env: Environment, ctx: State, ctx': State)
    requires SupportsInterp(e)
    requires EqState(ctx, ctx')
    ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e, env, ctx'))
  {
    // The proof should be similar to ``EqInterp_Expr_CanBeMapLifted`` (and actually
    // simpler), but I'm not sure how to efficiently factorize the two.
    assume false; // TODO: prove
  }

  lemma EqValue_Refl(v: WV)
    ensures EqValue(v, v)
    decreases v, 1
  {
    match v {
      case Unit => {}
      case Bool(_) => {}
      case Char(_) => {}
      case Int(_) => {}
      case Real(_) => {}
      case BigOrdinal(_) => {}
      case BitVector(_, _) => {}
      case Map(m) => {
        ValueTypeHeight_Children_Lem(v); // For termination
        forall x | x in m ensures EqValue(m[x], m[x]) {
          EqValue_Refl(m[x]);
        }
      }
      case Multiset(ms) => {}
      case Seq(sq) => {
        ValueTypeHeight_Children_Lem(v); // For termination
        forall i | 0 <= i < |sq| ensures EqValue(sq[i], sq[i]) {
          EqValue_Refl(sq[i]);
        }
      }
      case Set(st) => {}
      case Closure(ctx, vars, body) => {
        EqValue_Closure_Refl(v);
      }
    }
  }

  lemma BuildCallState_EqState(ctx: Context, ctx': Context, vars: seq<string>, argvs: seq<WV>, argvs': seq<WV>)
    requires WellFormedContext(ctx)
    requires WellFormedContext(ctx')
    requires |argvs| == |argvs'| == |vars|
    requires (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
    requires EqCtx(ctx, ctx')
    ensures
      var ctx1 := BuildCallState(ctx, vars, argvs);
      var ctx1' := BuildCallState(ctx', vars, argvs');
      EqState(ctx1, ctx1')
  {
    MapOfPairs_SeqZip_EqCtx(vars, argvs, argvs');
    var m := MapOfPairs(Seq.Zip(vars, argvs));
    var m' := MapOfPairs(Seq.Zip(vars, argvs'));
    reveal BuildCallState();
    var ctx1 := BuildCallState(ctx, vars, argvs);
    var ctx1' := BuildCallState(ctx', vars, argvs');
    reveal GEqCtx();
    assert ctx1.locals == ctx + m;
    assert ctx1'.locals == ctx' + m';
  }

  lemma EqValue_Closure_Refl(v: WV)
    requires v.Closure?
    ensures EqValue_Closure(v, v)
    decreases v, 0
  {
    reveal EqValue_Closure();

    var Closure(ctx, vars, body) := v;

    forall env: Environment, argvs: seq<WV>, argvs': seq<WV> |
      && |argvs| == |argvs'| == |vars|
      && (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs[i]) < ValueTypeHeight(v))
      && (forall i | 0 <= i < |vars| :: ValueTypeHeight(argvs'[i]) < ValueTypeHeight(v))
      && (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
      ensures
        var res := InterpCallFunctionBody(v, env, argvs);
        var res' := InterpCallFunctionBody(v, env, argvs');
        EqPureInterpResultValue(res, res')
    {
        var res := InterpCallFunctionBody(v, env, argvs);
        var res' := InterpCallFunctionBody(v, env, argvs');

        assert EqCtx(ctx, ctx) by {
          // It would be difficult to call a lemma like ``EqState_Refl`` here, because
          // of termination issues. However, we have that the values in the closure context
          // are smaller than the closure value itself, which allows us to recursively call
          // ``EqValue``.
          forall x | x in ctx ensures EqValue(ctx[x], ctx[x]) {
            EqValue_Refl(ctx[x]);
          }
          reveal GEqCtx();
        }

        var ctx1 := BuildCallState(ctx, vars, argvs);
        var ctx1' := BuildCallState(ctx, vars, argvs');
        BuildCallState_EqState(ctx, ctx, vars, argvs, argvs');
        assert EqState(ctx1, ctx1');

        reveal InterpCallFunctionBody();
        EqInterp_Expr_EqState(body, env, ctx1, ctx1');
        assert EqPureInterpResultValue(res, res');
    }
  }

  lemma EqState_Refl(ctx: State)
    ensures EqState(ctx, ctx)
  {
    reveal GEqCtx();
    EqValue_Refl_Forall();
  }

  lemma EqValue_Trans(v0: WV, v1: WV, v2: WV)
    requires EqValue(v0, v1)
    requires EqValue(v1, v2)
    ensures EqValue(v0, v2)
    decreases ValueTypeHeight(v0), 1
  {
    match v0 {
      case Unit => {}
      case Bool(_) => {}
      case Char(_) => {}
      case Int(_) => {}
      case Real(_) => {}
      case BigOrdinal(_) => {}
      case BitVector(_, _) => {}
      case Map(m0) =>
        ValueTypeHeight_Children_Lem(v0); // For termination
        forall x | x in m0 ensures EqValue(v0.m[x], v2.m[x]) {
          EqValue_Trans(v0.m[x], v1.m[x], v2.m[x]);
        }
      case Multiset(ms) => {}
      case Seq(sq) =>
        ValueTypeHeight_Children_Lem(v0); // For termination
        forall i | 0 <= i < |sq| ensures EqValue(v0.sq[i], v2.sq[i]) {
          EqValue_Trans(v0.sq[i], v1.sq[i], v2.sq[i]);
        }
      case Set(st) => {}
      case Closure(ctx, vars, body) =>
        EqValue_Closure_Trans(v0, v1, v2);
    }
  }

  lemma EqValue_Closure_Trans(v0: WV, v1: WV, v2: WV)
    requires v0.Closure?
    requires v1.Closure?
    requires v2.Closure?
    requires EqValue_Closure(v0, v1)
    requires EqValue_Closure(v1, v2)
    ensures EqValue_Closure(v0, v2)
    decreases ValueTypeHeight(v0), 0
  {
    reveal EqValue_Closure();

    var Closure(ctx0, vars0, body0) := v0;
    var Closure(ctx1, vars1, body1) := v1;
    var Closure(ctx2, vars2, body2) := v2;

    forall env: Environment, argvs0: seq<WV>, argvs2: seq<WV> |
      && |argvs0| == |argvs2| == |vars0|
      && (forall i | 0 <= i < |vars0| :: ValueTypeHeight(argvs0[i]) < ValueTypeHeight(v0))
      && (forall i | 0 <= i < |vars0| :: ValueTypeHeight(argvs2[i]) < ValueTypeHeight(v2))
      && (forall i | 0 <= i < |vars0| :: EqValue(argvs0[i], argvs2[i]))
      ensures
        var res0 := InterpCallFunctionBody(v0, env, argvs0);
        var res2 := InterpCallFunctionBody(v2, env, argvs2);
        EqPureInterpResultValue(res0, res2)
    {
        var res0 := InterpCallFunctionBody(v0, env, argvs0);
        var res2 := InterpCallFunctionBody(v2, env, argvs2);

        // Termination issue: we need to assume that the arguments' types have the
        // proper height. In practice, if the program is properly type checked, we
        // have:
        // - `TypeOf(v0) == TypeOf(v1) == TypeOf(v2)`
        // - `forall i, TypeOf(argvs0[i]) == TypeOf(argvs2[i])1
        // so the assumption is trivially true.
        assume (forall i | 0 <= i < |vars0| :: ValueTypeHeight(argvs0[i]) < ValueTypeHeight(v1));

        forall i | 0 <= i < |vars0| ensures EqValue(argvs0[i], argvs0[i]) {
          EqValue_Refl(argvs0[i]);
        }

        var res1 := InterpCallFunctionBody(v1, env, argvs0);
        if res0.Success? {
          var ov0 := res0.value;
          var ov1 := res1.value;
          var ov2 := res2.value;

          // Termination - same as above: if the program is well-typed, this is
          // trivially true.
          assume ValueTypeHeight(ov0) < ValueTypeHeight(v0);

          EqValue_Trans(ov0, ov1, ov2);

          assert EqPureInterpResultValue(res0, res2);
        }
        else {
          assert res1.Failure?;
          assert res2.Failure?;
        }
    }
  }

  lemma {:induction v, v'} EqValue_HasEqValue(v: WV, v': WV)
    requires EqValue(v, v')
    ensures HasEqValue(v) == HasEqValue(v')
  {}

  lemma EqValue_HasEqValue_Forall()
    ensures forall v: WV, v': WV | EqValue(v, v') :: HasEqValue(v) == HasEqValue(v')
  {
    forall v: WV, v': WV | EqValue(v, v') ensures HasEqValue(v) == HasEqValue(v') {
      EqValue_HasEqValue(v, v');
    }
  }

  lemma EqValue_HasEqValue_Eq(v: WV, v': WV)
    requires EqValue(v, v')
    ensures HasEqValue(v) == HasEqValue(v')
    ensures HasEqValue(v) ==> v == v'
  {
    EqValue_HasEqValue(v, v');
    if HasEqValue(v) || HasEqValue(v') {
      EqValueHasEq(v, v');
    }
  }

  lemma EqValue_HasEqValue_Eq_Forall()
    ensures forall v:WV, v':WV | EqValue(v, v') ::
      && (HasEqValue(v) == HasEqValue(v'))
      && (HasEqValue(v) ==> v == v')
    // This is one of the important lemmas for the proofs of equivalence.
    // The reason is that the interpreter often checks that some values
    // have a decidable equality (for instance, before inserting a value in
    // a set). When doing equivalence proofs, for instance to prove that the
    // same instruction evaluated in equivalent contexts generates equivalent
    // results, we often want:
    // - to know that the check succeeds in both cases, or fails in both cases
    // - to know that if it succeeded, then the valuevs are equal
  {
    forall v:WV, v':WV | EqValue(v, v')
      ensures
      && (HasEqValue(v) == HasEqValue(v'))
      && (HasEqValue(v) ==> v == v') {
        EqValue_HasEqValue_Eq(v, v');
    }
  }

  lemma EqValue_Refl_Forall()
    ensures forall v : WV :: EqValue(v, v)
  {
    forall v : WV | true
      ensures EqValue(v, v)
    {
      EqValue_Refl(v);
      assert EqValue(v, v);
    }
  }

  lemma EqState_Trans(ctx0: State, ctx1: State, ctx2: State)
    requires EqState(ctx0, ctx1)
    requires EqState(ctx1, ctx2)
    ensures EqState(ctx0, ctx2)
  {
    reveal GEqCtx();
    forall x | x in ctx0.locals.Keys ensures EqValue(ctx0.locals[x], ctx2.locals[x]) {
      EqValue_Trans(ctx0.locals[x], ctx1.locals[x], ctx2.locals[x]);
    }
  }

  predicate EqSeq<T(0)>(eq_values: (T,T) -> bool, vs: seq<T>, vs': seq<T>) {
    && |vs| == |vs'|
    && (forall i | 0 <= i < |vs| :: eq_values(vs[i], vs'[i]))
  }

  predicate EqMap<T(0,!new), U(0,!new)>(eq_values: (U,U) -> bool, vs: map<T, U>, vs': map<T, U>) {
    && vs.Keys == vs'.Keys
    && |vs| == |vs'|
    && (forall x | x in vs :: eq_values(vs[x], vs'[x]))
  }

  predicate EqPairs<T(0), U(0)>(same_t: (T,T) -> bool, same_u: (U,U) -> bool, v: (T,U), v': (T,U)) {
    && same_t(v.0, v'.0)
    && same_u(v.1, v'.1)
  }

  predicate EqSeqValue(vs: seq<WV>, vs': seq<WV>) {
    EqSeq(EqValue, vs, vs')
  }

  predicate EqMapValue(m: map<EqWV, WV>, m': map<EqWV,WV>) {
    && m.Keys == m'.Keys
    && |m| == |m'|
    && (forall x | x in m :: EqValue(m[x], m'[x]))
  }

  predicate EqSeqPairEqValueValue(vs: seq<(EqWV,WV)>, vs': seq<(EqWV,WV)>) {
    EqSeq((v: (EqWV,WV),v': (EqWV,WV)) => EqValue(v.0, v'.0) && EqValue(v.1, v'.1), vs, vs')
  }

  predicate EqEqValue(v: EqWV, v': EqWV) {
    EqValue(v, v')
  }

  predicate EqPairEqValueValue(v: (EqWV,WV), v': (EqWV,WV)) {
    EqPairs(EqEqValue, EqValue, v, v')
  }

  predicate EqInterpResultValue(res: InterpResult<WV>, res': InterpResult<WV>)
  {
    EqInterpResult(EqValue, res, res')
  }

  predicate EqInterpResultSeqValue(res: InterpResult<seq<WV>>, res': InterpResult<seq<WV>>)
  {
    EqInterpResult(EqSeqValue, res, res')
  }

  predicate GEqInterpResultSeq(eq: Equivs, res: InterpResult<seq<WV>>, res': InterpResult<seq<WV>>)
  {
    GEqInterpResult(eq.eq_state, (x, x') => EqSeq(eq.eq_value, x, x'), res, res')
  }

  predicate EqPureInterpResult<T(0)>(eq_values: (T,T) -> bool, res: PureInterpResult<T>, res': PureInterpResult<T>)
  {
    match (res, res') {
      case (Success(v), Success(v')) =>
        eq_values(v, v')
      case (Failure(_), Failure(_)) =>
        true
      case _ =>
        false
    }
  }

  predicate EqPureInterpResultValue(res: PureInterpResult<WV>, res': PureInterpResult<WV>)
  {
    EqPureInterpResult(EqValue, res, res')
  }

  predicate EqPureInterpResultSeqValue(res: PureInterpResult<seq<WV>>, res': PureInterpResult<seq<WV>>)
  {
    EqPureInterpResult(EqSeqValue, res, res')
  }

  predicate EqInterpResultSeq1Value(res: InterpResult<WV>, res': InterpResult<seq<WV>>)
  {
    match (res, res') {
      case (Success(Return(v,ctx)), Success(Return(sv,ctx'))) =>
        && |sv| == 1
        && EqValue(v, sv[0])
        && EqState(ctx, ctx')
      case (Failure(_), Failure(_)) =>
        true
      case _ =>
        false
    }
  }

  predicate EqInterpResultValue_Strong(res: InterpResult<WV>, res': InterpResult<WV>)
    // Equality predicate about results, using a *strong* equality rather than our weak
    // notion of equivalence.
  {
    match (res, res') {
      case (Success(Return(v,ctx)), Success(Return(v',ctx'))) =>
        && v == v'
        && ctx == ctx'
      case (Failure(err), Failure(err')) =>
        err == err'
      case _ =>
        false
    }
  }

  predicate EqInterpResultSeq1Value_Strong(res: InterpResult<WV>, res': InterpResult<seq<WV>>)
    // Equality predicate about results, using a *strong* equality rather than our weak
    // notion of equivalence.
  {
    match (res, res') {
      case (Success(Return(v,ctx)), Success(Return(sv,ctx'))) =>
        && sv == [v]
        && ctx == ctx'
      case (Failure(err), Failure(err')) =>
        err == err'
      case _ =>
        false
    }
  }

  // TODO: make opaque?
  predicate GEqInterp(eq: Equivs, e: Exprs.T, e': Exprs.T)
    // This is the important, generic equivalence relation over expressions.
  {
    SupportsInterp(e) ==>
    (&& SupportsInterp(e')
     && forall env, ctx, ctx' | eq.eq_state(ctx, ctx') ::
       GEqInterpResult(eq.eq_state, eq.eq_value,
                       InterpExpr(e, env, ctx),
                       InterpExpr(e', env, ctx')))
  }

  function Mk_EqInterp(eq: Equivs): (Expr, Expr) -> bool {
    (e, e') => GEqInterp(eq, e, e')
  }

  // TODO(SMH): make opaque?
  predicate EqInterp(e: Exprs.T, e': Exprs.T)
    // The important equivalence relation over expressions.
  {
    GEqInterp(EQ(EqValue, Mk_EqState(EqValue)), e, e')
  }

  // TODO(SMH): make opaque?
  predicate EqInterpBlockExprs(es: seq<Exprs.T>, es': seq<Exprs.T>)
  {
    Seq_All(SupportsInterp, es) ==>
    (&& Seq_All(SupportsInterp, es')
     && forall env, ctx, ctx' | EqState(ctx, ctx') ::
       EqInterpResultValue(
                      InterpBlock_Exprs(es, env, ctx),
                      InterpBlock_Exprs(es', env, ctx')))
  }

  lemma EqInterp_Refl(e: Exprs.T)
    ensures EqInterp(e, e)
  {
    if SupportsInterp(e) {
      forall env, ctx, ctx' | EqState(ctx, ctx')
        ensures
          EqInterpResultValue(
                       InterpExpr(e, env, ctx),
                       InterpExpr(e, env, ctx'))
      {
        EqInterp_Expr_EqState(e, env, ctx, ctx');
      }
    }
  }

  lemma EqInterpBlockExprs_Inst(es: seq<Exprs.T>, es': seq<Exprs.T>, env: Environment, ctx: State, ctx': State)
    requires EqInterpBlockExprs(es, es')
    requires Seq_All(SupportsInterp, es)
    requires EqState(ctx, ctx')
    ensures  EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es', env, ctx'))
  {}

  predicate All_Rel_Forall<A, B>(rel: (A,B) -> bool, xs: seq<A>, ys: seq<B>)
  {
    && |xs| == |ys|
    && forall i | 0 <= i < |xs| :: rel(xs[i], ys[i])
  }

  lemma EqInterp_Seq_Refl(es: seq<Exprs.T>)
    ensures All_Rel_Forall(EqInterp, es, es)
  {
    forall i | 0 <= i < |es| ensures EqInterp(es[i], es[i]) {
      EqInterp_Refl(es[i]);
    }
  }

  lemma EqInterp_Trans(e0: Exprs.T, e1: Exprs.T, e2: Exprs.T)
    requires EqInterp(e0, e1)
    requires EqInterp(e1, e2)
    ensures EqInterp(e0, e2)
  {
    if SupportsInterp(e0) {
      forall env, ctx, ctx' | EqState(ctx, ctx')
        ensures EqInterpResultValue(InterpExpr(e0, env, ctx), InterpExpr(e2, env, ctx'))
      {
        EqState_Refl(ctx);
        assert EqState(ctx, ctx);
        var res0 := InterpExpr(e0, env, ctx);
        var res1 := InterpExpr(e1, env, ctx);
        var res2 := InterpExpr(e2, env, ctx');
        assert EqInterpResultValue(res0, res1);
        assert EqInterpResultValue(res1, res2);

        if res0.Success? {
          EqValue_Trans(res0.value.ret, res1.value.ret, res2.value.ret);
          EqState_Trans(res0.value.ctx, res1.value.ctx, res2.value.ctx);
        }
        else {}
      }
    }
    else {}
  }

  predicate RelIsTransitive<T(!new)>(rel: (T, T) -> bool) {
    forall x0, x1, x2 | rel(x0, x1) && rel(x1, x2) :: rel(x0, x2)
  }

  lemma EqInterp_IsTransitive()
    ensures RelIsTransitive(EqInterp)
  {
    forall e0, e1, e2 | EqInterp(e0, e1) && EqInterp(e1, e2) ensures EqInterp(e0, e2) {
      EqInterp_Trans(e0, e1, e2);
    }
  }

  lemma InterpExprs1_Strong_Eq(e: Expr, env: Environment, ctx: State)
    requires SupportsInterp(e)
    ensures forall e' | e' in [e] :: SupportsInterp(e')
    ensures EqInterpResultSeq1Value_Strong(InterpExpr(e, env, ctx), InterpExprs([e], env, ctx))
    // Auxiliary lemma: evaluating a sequence of one expression is equivalent to evaluating
    // the single expression.
  {
    reveal InterpExprs();
    var es := [e];
    var es' := es[1..];
    assert es' == [];

    var e_res := InterpExpr(e, env, ctx);
    var es_res := InterpExprs([e], env, ctx);

    if e_res.Success? {
      var Return(v, ctx1) := e_res.value;

      assert InterpExprs(es', env, ctx1) == Success(Return([], ctx1));
      assert es_res == Success(Return([v] + [], ctx1));
    }
    else {
      // Trivial
    }
  }

  lemma InterpBlock_Exprs_Refl(es: seq<Expr>, env: Environment, ctx: State, ctx': State)
    requires Seq_All(SupportsInterp, es)
    requires EqState(ctx, ctx')
    ensures EqInterpResultValue(InterpBlock_Exprs(es, env, ctx), InterpBlock_Exprs(es, env, ctx'))
  {
    reveal InterpBlock_Exprs();
    if es == [] {}
    else {
       // Evaluate the first expression
      var res0 := InterpExpr(es[0], env, ctx);
      var res0' := InterpExpr(es[0], env, ctx');
      EqInterp_Refl(es[0]);
      EqInterp_Inst(es[0], es[0], env, ctx, ctx');

      // Evaluate the remaining expressions
      if res0.Success? && res0.value.ret == V.Unit {
        var Return(_, ctx0) := res0.value;
        var Return(_, ctx0') := res0'.value;

        InterpBlock_Exprs_Refl(es[1..], env, ctx0, ctx0');
      }
      else {
        // Trivial
      }
    }
  }

  lemma EqInterp_Inst(e: Exprs.T, e': Exprs.T, env: Environment, ctx: State, ctx': State)
    requires SupportsInterp(e)
    requires EqInterp(e, e')
    requires EqState(ctx, ctx')
    ensures SupportsInterp(e')
    ensures EqInterpResultValue(InterpExpr(e, env, ctx), InterpExpr(e', env, ctx'))
  // We use this lemma because sometimes quantifiers are are not triggered.
  {}

  lemma InterpExprs_GEqInterp_Inst(
    eq: Equivs, es: seq<Expr>, es': seq<Expr>, env: Environment, ctx: State, ctx': State)
    requires forall e | e in es :: SupportsInterp(e)
    requires All_Rel_Forall(Mk_EqInterp(eq), es, es')
    requires eq.eq_state(ctx, ctx')
    ensures forall e | e in es' :: SupportsInterp(e)
    ensures GEqInterpResultSeq(eq, InterpExprs(es, env, ctx), InterpExprs(es', env, ctx'))
  // Auxiliary lemma: if two sequences contain equivalent expressions, evaluating those two
  // sequences in equivalent contexts leads to equivalent results.
  // This lemma is written generically over the equivalence relations over the states and
  // values. We don't do this because it seems elegant: we do this as a desperate attempt
  // to reduce the context size, while we are unable to use the `opaque` attribute on
  // some definitions (``EqValue`` in particular).
  {
    reveal InterpExprs();

    var res := InterpExprs(es, env, ctx);
    var res' := InterpExprs(es', env, ctx');
    if es == [] {
      assert res == Success(Return([], ctx));
      assert res' == Success(Return([], ctx'));
      assert eq.eq_state(ctx, ctx');
    }
    else {
      // Evaluate the first expression in the sequence
      var res1 := InterpExpr(es[0], env, ctx);
      var res1' := InterpExpr(es'[0], env, ctx');

      match res1 {
        case Success(Return(v, ctx1)) => {
          // TODO: the following statement generates an error.
          // See: https://github.com/dafny-lang/dafny/issues/2258
          //var Success(Return(v', ctx1')) := res1;
          var Return(v', ctx1') := res1'.value;
          assert eq.eq_value(v, v');
          assert eq.eq_state(ctx1, ctx1');

          // Evaluate the rest of the sequence
          var res2 := InterpExprs(es[1..], env, ctx1);
          var res2' := InterpExprs(es'[1..], env, ctx1');

          // Recursive call
          InterpExprs_GEqInterp_Inst(eq, es[1..], es'[1..], env, ctx1, ctx1');

          match res2 {
            case Success(Return(vs, ctx2)) => {
              var Return(vs', ctx2') := res2'.value;
              assert EqSeq(eq.eq_value, vs, vs');
              assert eq.eq_state(ctx2, ctx2');

            }
            case Failure(_) => {
              assert res2'.Failure?;
            }
          }
        }
        case Failure(_) => {
          assert res1'.Failure?;
        }
      }
    }
  }

  lemma InterpExprs_EqInterp_Inst(es: seq<Expr>, es': seq<Expr>, env: Environment, ctx: State, ctx': State)
    requires forall e | e in es :: SupportsInterp(e)
    requires All_Rel_Forall(EqInterp, es, es')
    requires EqState(ctx, ctx')
    ensures forall e | e in es' :: SupportsInterp(e)
    ensures EqInterpResultSeqValue(InterpExprs(es, env, ctx), InterpExprs(es', env, ctx'))
  // Auxiliary lemma: if two sequences contain equivalent expressions, evaluating those two
  // sequences in equivalent contexts leads to equivalent results.
  {
    InterpExprs_GEqInterp_Inst(EQ(EqValue, EqState), es, es', env, ctx, ctx');
  }

  lemma Map_PairOfMapDisplaySeq(e: Interp.Expr, e': Interp.Expr, argvs: seq<WV>, argvs': seq<WV>)
    requires EqSeqValue(argvs, argvs')
    ensures EqPureInterpResult(EqSeqPairEqValueValue,
                               Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv)),
                               Seq.MapResult(argvs', argv => PairOfMapDisplaySeq(e', argv)))
  {
    if argvs == [] {}
    else {
      var argv := argvs[0];
      var argv' := argvs'[0];
      assert EqValue(argv, argv');
      assert EqValue(argv, argv');

      var res0 := PairOfMapDisplaySeq(e, argv);
      var res0' := PairOfMapDisplaySeq(e', argv');

      EqValue_HasEqValue_Eq_Forall();
      if res0.Success? {
        assert res0'.Success?;
        assert EqPureInterpResult(EqPairEqValueValue, res0, res0');

        reveal Seq.MapResult();
        Map_PairOfMapDisplaySeq(e, e', argvs[1..], argvs'[1..]);
      }
      else {
        // Trivial
      }
    }
  }

  lemma MapOfPairs_EqArgs(argvs: seq<(EqWV, WV)>, argvs': seq<(EqWV, WV)>)
    requires EqSeqPairEqValueValue(argvs, argvs')
    ensures EqMap(EqValue, MapOfPairs(argvs), MapOfPairs(argvs'))
  {
    if argvs == [] {}
    else {
      var lastidx := |argvs| - 1;
      EqValueHasEq_Forall();
      MapOfPairs_EqArgs(argvs[..lastidx], argvs'[..lastidx]);
    }
  }

  lemma InterpMapDisplay_EqArgs(e: Interp.Expr, e': Interp.Expr, argvs: seq<WV>, argvs': seq<WV>)
    requires EqSeqValue(argvs, argvs')
    ensures EqPureInterpResult(EqMapValue, InterpMapDisplay(e, argvs), InterpMapDisplay(e', argvs')) {
    var res0 := Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv));
    var res0' := Seq.MapResult(argvs', argv => PairOfMapDisplaySeq(e', argv));

    Map_PairOfMapDisplaySeq(e, e', argvs, argvs');
    EqValue_HasEqValue_Eq_Forall();

    match res0 {
      case Success(pairs) => {
        var pairs' := res0'.value;

        MapOfPairs_EqArgs(pairs, pairs');

        var m := MapOfPairs(pairs);
        var m' := MapOfPairs(pairs');
        assert EqMapValue(m, m');
      }
      case Failure(_) => {
        // Trivial
      }
    }
  }

  lemma MapOfPairs_EqCtx(pl: seq<(string, WV)>, pl': seq<(string, WV)>)
    requires |pl| == |pl'|
    requires (forall i | 0 <= i < |pl| :: pl[i].0 == pl'[i].0)
    requires (forall i | 0 <= i < |pl| :: EqValue(pl[i].1, pl'[i].1))
    ensures
      var m := MapOfPairs(pl);
      var m' := MapOfPairs(pl');
      EqCtx(m, m')
  {
    reveal GEqCtx();
    if pl == [] {}
    else {
      var lastidx := |pl| - 1;
      MapOfPairs_EqCtx(pl[..lastidx], pl'[..lastidx]);
    }
  }

  // (SMH) I don't understand why I need to use vcs_split_on_every_assert on this one.
  // For some strange reason it takes ~20s to verify with this, and timeouts without.
  lemma {:vcs_split_on_every_assert}
  MapOfPairs_SeqZip_EqCtx(vars: seq<string>, argvs: seq<WV>, argvs': seq<WV>)
    requires |argvs| == |argvs'| == |vars|
    requires (forall i | 0 <= i < |vars| :: EqValue(argvs[i], argvs'[i]))
    ensures
      var m := MapOfPairs(Seq.Zip(vars, argvs));
      var m' := MapOfPairs(Seq.Zip(vars, argvs'));
      EqCtx(m, m')
  {
    var pl := Seq.Zip(vars, argvs);
    var pl' := Seq.Zip(vars, argvs');

    assert |pl| == |pl'|;
    assert forall i | 0 <= i < |pl| :: pl[i].0 == pl'[i].0;
    assert forall i | 0 <= i < |pl| :: EqValue(pl[i].1, pl'[i].1);

    reveal GEqCtx();
    MapOfPairs_EqCtx(pl, pl');
  }

  lemma InterpBlock_Exprs_Eq_Append(e: Expr, e': Expr, tl: seq<Expr>, tl': seq<Expr>, env: Environment, ctx: State, ctx': State)
    requires SupportsInterp(e)
    requires SupportsInterp(e')
    requires Seq_All(SupportsInterp, tl)
    requires Seq_All(SupportsInterp, tl')
    requires EqState(ctx, ctx')
    requires EqInterp(e, e')
    requires EqInterpBlockExprs(tl, tl')
    requires |tl| > 0
    ensures EqInterpResultValue(InterpBlock_Exprs([e] + tl, env, ctx), InterpBlock_Exprs([e'] + tl', env, ctx'))
    // Auxiliary lemma for the proofs about transformations operating on blocks. This is especially
    // useful when those transformations might update the length of the sequence of expressions
    // in the blocks. The proof is a bit tricky, because the case where the sequence has length 1
    // is a special case in the definition of ``EqInterpBlock_Exprs``.
  {
    var es := [e] + tl;
    var es' := [e'] + tl';
    assert e == es[0];

    reveal InterpBlock_Exprs();

    // Evaluate the first expression
    var res0 := InterpExpr(e, env, ctx);
    var res0' := InterpExpr(e', env, ctx');
    EqInterp_Inst(e, e', env, ctx, ctx');

    // We need to make a case disjunction on whether the length of the concatenated sequences is
    // > 1 or not
    if |tl'| >= 1 {
      // The "regular" case

      // Evaluate the remaining expressions
      if res0.Success? && res0.value.ret == V.Unit {
        var Return(_, ctx0) := res0.value;
        var Return(_, ctx0') := res0'.value;

        var res1 := InterpBlock_Exprs(tl, env, ctx0);
        var res1' := InterpBlock_Exprs(tl', env, ctx0');

        EqInterpBlockExprs_Inst(tl, tl', env, ctx0, ctx0');
      }
      else {
        // Trivial
      }
    }
    else {
      // Degenerate case
      assert |tl'| == 0;

      if res0.Success? {
        var Return(v, ctx0) := res0.value;
        var Return(v', ctx0') := res0'.value;

        if v == V.Unit {
          assert v' == V.Unit;
          EqInterpBlockExprs_Inst(tl, tl', env, ctx0, ctx0');
        }
        else {
          assert v' != V.Unit;

          // TODO(SMH): update EqInterp so that this works (evaluating `es` will fail if `e` doesn't
          // evaluate to `Unit`)
          assume false; // TODO: prove
        }
      }
      else {
        // Trivial
      }
    }
  }
}

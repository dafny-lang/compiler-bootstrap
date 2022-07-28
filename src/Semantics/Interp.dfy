include "../Utils/Library.dfy"
include "../AST/Syntax.dfy"
include "../AST/Predicates.dfy"
include "Values.dfy"

module Bootstrap.Semantics.Interp {
  import Utils.Lib.Math
  import Utils.Lib.Debug
  import Utils.Lib.Seq

  import V = Values
  import AST.Syntax
  import AST.Syntax.Types
  import AST.Syntax.Exprs

  import opened Utils.Lib.Datatypes
  import opened AST.Predicates

  predicate method EagerOpSupportsInterp(op: Exprs.EagerOp) {
    match op {
      case UnaryOp(uop) => !uop.MemberSelect?
      case BinaryOp(bop) => !bop.BV? && !bop.Datatypes?
      case TernaryOp(top) => true
      case Builtin(Display(_)) => true
      case Builtin(Print()) => false
      case FunctionCall() => true
      case DataConstructor(name, typeArgs) => Debug.TODO(false)
    }
  }

  predicate method SupportsInterp1(e: Exprs.T) {
    Exprs.WellFormed(e) &&
    match e {
      case Var(_) => true
      case Literal(lit) => true
      case Abs(vars, body) => true
      case Apply(Lazy(op), args) => true
      case Apply(Eager(op), args) => EagerOpSupportsInterp(op)
      case Bind(vars, vals, body) => true
      case VarDecl(vars, ovals) => true
      case Update(vars, vals) => true
      case Block(stmts) => true
      case If(cond, thn, els) => true
    }
  }

  // TODO: I'm not sure it was worth making this opaque.
  predicate method {:opaque} SupportsInterp(e: Exprs.T) {
    Predicates.Deep.All_Expr(e, SupportsInterp1)
  }

  // TODO: rewrite as a shallow predicate applied through ``v.All``?
  predicate method WellFormedEqValue(v: V.T)
  // This predicate gives the constrainst we need to be able to *define* our equivalence relation
  // over values and actually *use* this relati\on to prove equivalence properties between expressions.
  //
  // The difficult point is linked to closures: when we apply transformations to the code, we often
  // apply them in a deep manner to the expressions (i.e., to all the subexpressions of an expression).
  // The problem is that it can have an effect on the closure values generated through the execution
  // by modifying their bodies, leading to discrepancies in the execution of the code (imagine the case
  // where we use closures as keys inside of maps).
  // The good news is that when those cases happen, we actually try to use an equality over values
  // which don't have a decidable equality: we solve the problem by forcing some subvalues to have
  // a decidable equality.
  {
    match v {
      case Unit => true
      case Bool(b) => true
      case Char(c) => true
      case Int(i) => true
      case Real(r) => true
      case BigOrdinal(o) => true
      case BitVector(width, val) =>
        0 <= val < Math.IntPow(2, width)
      case Map(m) =>
        && (forall x | x in m :: HasEqValue(x))
        && (forall x | x in m :: WellFormedEqValue(x) && WellFormedEqValue(m[x]))
      case Multiset(ms) =>
        && HasEqValue(v)
        && (forall x | x in ms :: WellFormedEqValue(x))
      case Seq(sq) =>
        && (forall x | x in sq :: WellFormedEqValue(x))
      case Set(st) =>
        && HasEqValue(v)
        && (forall x | x in st :: WellFormedEqValue(x))
      case Closure(ctx, vars, body) =>
        // TODO: is that enough?
        && (forall x | x in ctx.Values :: WellFormedEqValue(x))
    }
  }

  // TODO: rename to ValueHasEq
  predicate method HasEqValue(v: V.T)
  // Return true if the value supports a decidale equality.
  //
  // Note that this is a bit subtle for collections: any empt\y collection supports a decidable
  // equality, but non-empty collections support a decidable equality only if their elements
  // support one.
  {
    match v {
      case Unit => true
      case Bool(b) => true
      case Char(c) => true
      case Int(i) => true
      case Real(r) => true
      case BigOrdinal(o) => true
      case BitVector(width, val) => true
      case Map(m) =>
        forall x | x in m :: HasEqValue(x) && HasEqValue(m[x])
      case Multiset(ms) =>
        forall x | x in ms :: HasEqValue(x)
      case Seq(sq) =>
        forall x | x in sq :: HasEqValue(x)
      case Set(st) =>
        forall x | x in st :: HasEqValue(x)
      case Closure(ctx, vars, body) => false
    }
  }

  predicate method WellFormedValue1(v: V.T)
  // The *shallow* well-formedness predicate for values manipulated by the interpreter.
  {
    && v.Closure? ==> SupportsInterp(v.body)
    && v.WellFormed1()
  }

  predicate method WellFormedValue(v: V.T) {
    // Rk.: ``Value.All`` goes inside the closure contexts
    && v.All(WellFormedValue1)
    && WellFormedEqValue(v)
  }

  predicate method WellFormedContext(ctx: V.Context) {
    forall v' | v' in ctx.Values :: WellFormedValue(v')
  }

  type Type = Types.T
  type Context = c: V.Context | WellFormedContext(c)
  type Value = v: V.T | WellFormedValue(v) witness V.Bool(false)
  type Expr = e: Exprs.T | SupportsInterp(e) witness (reveal SupportsInterp(); Exprs.Literal(Exprs.LitInt(0)))

  // The type of well-formed values with a decidable equality
  type EqWV = v: V.T | WellFormedValue(v) && HasEqValue(v) witness V.Bool(false)

  // DISCUSS: If we don't use this, sometimes Z3 fails to see that `V.Unit` is well-formed. It seems
  // to happen when we use nested subset types, for instance: `Success(Return(V.Unit, ctx))`.
  const Unit: Value := V.Unit

  // We need a value type height to prove that some functions terminate.
  function {:axiom} ValueTypeHeight(v: Value): nat

  // Axiom: the children of a collection have a smaller type than the collection's type
  lemma {:axiom} ValueTypeHeight_Children_Lem(v: Value)
    requires v.Map? || v.Multiset? || v.Seq? || v.Set?
    ensures forall x | x in v.Children() :: ValueTypeHeight(x) < ValueTypeHeight(v)
    // Special case for the keys of a map
    ensures v.Map? ==> (forall x | x in v.m :: ValueTypeHeight(x) < ValueTypeHeight(v))

  predicate InterpResultPred<A(0)>(p: (A,State) -> bool, r: InterpResult<A>) {
    match r {
      case Success(Return(x, ctx)) => p(x, ctx)
      case Failure(_) => true
    }
  }

  predicate PureInterpResultPred<A(0)>(p: A -> bool, r: PureInterpResult<A>) {
    match r {
      case Success(x) => p(x)
      case Failure(_) => true
    }
  }

  // TODO(SMH): `locals` may not be an appropriate name.
  datatype State =
    State(locals: Context := map[], rollback: Context := map[])
  {
    static const Empty := State(map[], map[]) // BUG(https://github.com/dafny-lang/dafny/issues/2120)
  }

  datatype Environment =
    Environment(fuel: nat, globals: Context := map[])

  datatype InterpReturn<+A> =
    | Return(ret: A, ctx: State)

  // FIXME many "Invalid" below should really be type errors

  datatype InterpError =
    | OutOfFuel(fn: Value)
    | TypeError(e: Expr, value: Value, expected: Type) // TODO rule out type errors through Wf predicate?
    | Invalid(e: Expr) // TODO rule out in Wf predicate?
    | OutOfIntBounds(x: int, low: Option<int>, high: Option<int>)
    | OutOfSeqBounds(collection: Value, idx: Value)
    | OutOfMapDomain(collection: Value, idx: Value)
    | UnboundVariable(v: string)
    | SignatureMismatch(vars: seq<string>, argvs: seq<Value>)
    | DivisionByZero
  {
    function method ToString() : string {
      match this // TODO include values in messages
        case OutOfFuel(fn) => "Too many function evaluations"
        case TypeError(e, value, expected) => "Type mismatch"
        case Invalid(e) => "Invalid expression"
        case OutOfIntBounds(x, low, high) => "Out-of-bounds value"
        case OutOfSeqBounds(v, i) => "Index out of sequence bounds"
        case OutOfMapDomain(v, i) => "Missing key in map"
        case UnboundVariable(v) => "Unbound variable '" + v + "'"
        case SignatureMismatch(vars, argvs) => "Wrong number of arguments in function call"
        case DivisionByZero() => "Division by zero"
    }
  }

  type InterpResult<+A> =
    Result<InterpReturn<A>, InterpError>

  type PureInterpResult<+A> =
    Result<A, InterpError>

  function method LiftPureResult<A>(ctx: State, r: PureInterpResult<A>)
    : InterpResult<A>
  {
    var v :- r;
    Success(Return(v, ctx))
  }

  function method Eval(e: Expr, env: Environment, ctx: State)
    : InterpResult<Value>
  {
    InterpExpr(e, env, ctx)
  }

  function method VarsToNames(vars: seq<Exprs.Var>): seq<string> {
    Seq.Map((v: Exprs.Var) => v.name, vars)
  }

  function method {:opaque} InterpExpr(e: Expr, env: Environment, ctx: State)
    : InterpResult<Value>
    decreases env.fuel, e, 1
  {
    reveal SupportsInterp();
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    match e {
      case Var(v) =>
        LiftPureResult(ctx, InterpVar(v, ctx, env))

      case Abs(vars, body) =>
        var cv: V.T := V.Closure(ctx.locals, vars, body);
        assert WellFormedValue(cv); // TODO: prove
        Success(Return(cv, ctx))

      case Literal(lit) =>
        Success(Return(InterpLiteral(lit), ctx))

      case Apply(Lazy(op), args: seq<Expr>) =>
        // This is ``InterpLazy`` inlined.
        // See the comments for the ``Block`` case.
        reveal SupportsInterp();
        Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
        var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
        var Return(v0, ctx0) :- InterpExpr(e0, env, ctx);
        :- NeedType(e0, v0, Type.Bool);
        match (op, v0) {
          case (And, Bool(false)) => Success(Return(V.Bool(false), ctx0))
          case (Or,  Bool(true))  => Success(Return(V.Bool(true), ctx0))
          case (Imp, Bool(false)) => Success(Return(V.Bool(true), ctx0))
          case (_,   Bool(b)) =>
            assert op in {Exprs.And, Exprs.Or, Exprs.Imp};
            var Return(v1, ctx1) :- InterpExpr(e1, env, ctx0);
            :- NeedType(e1, v1, Type.Bool);
            Success(Return(v1, ctx1))
        }

      case Apply(Eager(op), args: seq<Expr>) =>
        var Return(argvs, ctx) :- InterpExprs(args, env, ctx);
        LiftPureResult(ctx, match op {
            case UnaryOp(op: UnaryOp) =>
              InterpUnaryOp(e, op, argvs[0])
            case BinaryOp(bop: BinaryOp) =>
              assert !bop.BV? && !bop.Datatypes?;
              InterpBinaryOp(e, bop, argvs[0], argvs[1])
            case TernaryOp(top: TernaryOp) =>
              InterpTernaryOp(e, top, argvs[0], argvs[1], argvs[2])
            case Builtin(Display(ty)) =>
              InterpDisplay(e, ty.kind, argvs)
            case FunctionCall() =>
              InterpFunctionCall(e, env, argvs[0], argvs[1..])
          })

      case Bind(bvars, vals: seq<Expr>, body: Expr) =>
        // This is ``InterpBind`` inlined (see the discussion for the ``Block`` case)
        var vars := VarsToNames(bvars);
        // A bind acts like a scope containing variable declarations:
        // - Open a scope
        var ctx1 := StartScope(ctx);
        // - Evaluate the rhs
        var Return(vals, ctx2) :- InterpExprs(vals, env, ctx1);
        // - Save the shadowed variables to the rollback
        var ctx3 := SaveToRollback(ctx2, vars);
        // - Augment the context with the new bindings
        var ctx4 := ctx3.(locals := AugmentContext(ctx3.locals, vars, vals));
        // - Execute the body
        var Return(v, ctx5) :- InterpExpr(body, env, ctx4);
        // - End the scope
        var ctx6 := EndScope(ctx, ctx5);
        // Return
        Success(Return(v, ctx6))

      case VarDecl(vdecls, ovals) =>
        var vars := VarsToNames(vdecls);
        // Evaluate the rhs, if there is
        if ovals.Some? then
          var Return(vals, ctx) :- InterpExprs(ovals.value, env, ctx);
          // Save the variables to the rollback context
          var ctx := SaveToRollback(ctx, vars);
          // Augment the context with the new bindings
          var ctx := ctx.(locals := AugmentContext(ctx.locals, vars, vals));
          // Continue
          Success(Return(Unit, ctx))
        else
          // Save the variables to the rollback context
          var ctx := SaveToRollback(ctx, vars);
          // Continue
          Success(Return(Unit, ctx))

      case Update(vars, vals) =>
        var Return(vals, ctx) :- InterpExprs(vals, env, ctx);
        // DISCUSS: we need to check that the variables have been declared, but there is actually
        // no way to do that for now (a variable declared but not initialized doesn't appear in the
        // environment - a variable declaration may only update the rollback context). But is not
        // checking that variables have been declared really a problem?
        var ctx := ctx.(locals := AugmentContext(ctx.locals, vars, vals));
        Success(Return(Unit, ctx))

      case Block(stmts) =>
        // This is ``InterpBlock`` inlined. We don't call ``InterpBlock`` on purpose because
        // then ``InterpBlock`` and ``InterpExpr`` would be mutually recursive, and unfolding
        // ``InterpBlock`` to reveal the call to ``InterpBlock_Exprs`` would require some fuel.
        // This lead to a lot of problems in the past, forcing us to write the call to ``InterpBlock``
        // just to allow one more level of unfolding, which is extremely annoying (the process of
        // debugging proofs when you don't have such issues in mind is tedious). We still provide
        // ``InterpBlock`` as a convenience function, and enforce it is the same as the ``Block``
        // case of ``InterpExpr` through the ``InterpBlock_Correct`` lemma.
        var ctx1 := StartScope(ctx);
        var Return(v, ctx2) :- InterpBlock_Exprs(stmts, env, ctx1);
        var ctx3 := EndScope(ctx, ctx2);
        Success(Return(v, ctx3))
      case If(cond, thn, els) =>
        var Return(condv, ctx) :- InterpExpr(cond, env, ctx);
        :- NeedType(e, condv, Type.Bool);
        if condv.b then InterpExpr(thn, env, ctx) else InterpExpr(els, env, ctx)
    }
  }

  function method InterpVar(v: string, ctx: State, env: Environment)
    : PureInterpResult<Value>
  {
    match TryGetVariable(ctx.locals, v, UnboundVariable(v))
      case Success(val) => Success(val)
      case Failure(err) => TryGetVariable(env.globals, v, err)
  }

  function method {:opaque} TryGetVariable(ctx: Context, k: string, err: InterpError)
    : (r: PureInterpResult<Value>)
    ensures r.Success? ==> k in ctx && r.value == ctx[k]
    ensures r.Failure? ==> k !in ctx && r.error == err
  {
    TryGet(ctx, k, err)
  }

  function method {:opaque} TryGet<K, V>(m: map<K, V>, k: K, err: InterpError)
    : (r: PureInterpResult<V>)
    ensures r.Success? ==> k in m && r.value == m[k]
    ensures r.Failure? ==> k !in m && r.error == err
  {
    if k in m then Success(m[k]) else Failure(err)
  }

  function method TryGetPair<K, V>(m: map<K, V>, k: K, err: InterpError)
    : (r: PureInterpResult<(K, V)>)
    ensures r.Success? ==> k in m && r.value == (k, m[k])
    ensures r.Failure? ==> k !in m && r.error == err
  {
    if k in m then Success((k, m[k])) else Failure(err)
  }

  function method MapOfPairs<K, V>(pairs: seq<(K, V)>)
    : (m: map<K, V>)
    ensures forall k | k in m :: (k, m[k]) in pairs
  {
    if pairs == [] then map[]
    else
      var lastidx := |pairs| - 1;
      MapOfPairs(pairs[..lastidx])[pairs[lastidx].0 := pairs[lastidx].1]
  }

  // DISCUSS: using this function *inside* the interpreter is a bad idea, because then it is mutually
  // recursive with all the other ``Interp...`` functions, and unfolding it requires fuel, which means
  // Z3 often doesn't see the call to ``InterpExpr`` inside, making some proofs require more work than
  // needed (for instance by forcing the user to introduce a call to ``InterpExprWithType`` in the
  // context to allow the unfolding). For this reason, whenever we need to use ``InterpExprWithType``
  // inside the interpreter definitions, we inline its body.
  // We still keep this definition because it provides a convenient utility for the rest of the project.
  function method InterpExprWithType(e: Expr, ty: Type, env: Environment, ctx: State)
    : (r: InterpResult<Value>)
    decreases env.fuel, e, 2
    ensures r.Success? ==> r.value.ret.HasType(ty)
  {
    reveal SupportsInterp();
    var Return(val, ctx) :- InterpExpr(e, env, ctx);
    :- NeedType(e, val, ty);
    Success(Return(val, ctx))
  }

  function method NeedType(e: Expr, val: Value, ty: Type)
    : (r: Outcome<InterpError>)
    ensures r.Pass? ==> val.HasType(ty)
  {
    Need(val.HasType(ty), TypeError(e, val, ty))
  }

  function method NeedTypes(es: seq<Expr>, vs: seq<Value>, ty: Type)
    : (r: Outcome<InterpError>)
    requires |es| == |vs|
    decreases |es|
    // DISCUSS: Replacing this with <==> doesn't verify
    ensures r.Pass? ==> forall v | v in vs :: v.HasType(ty)
    ensures r.Pass? <== forall v | v in vs :: v.HasType(ty)
  {
    if es == [] then
      assert vs == []; Pass
    else
      // DISCUSS: No `:-` for outcomes?
      // DISCUSS: should match accept multiple discriminands? (with lazy evaluation?)
      match NeedType(es[0], vs[0], ty)
        case Pass =>
          assert vs[0].HasType(ty);
          match NeedTypes(es[1..], vs[1..], ty) { // TODO check that compiler does this efficiently
            case Pass => assert forall v | v in vs[1..] :: v.HasType(ty); Pass
            case fail => fail
          }
        case fail => fail
  }

  function method {:opaque} InterpExprs(es: seq<Expr>, env: Environment, ctx: State)
    : (r: InterpResult<seq<Value>>)
    decreases env.fuel, es, 0
    ensures r.Success? ==> |r.value.ret| == |es|
  { // TODO generalize into a FoldResult function
    reveal SupportsInterp();
    if es == [] then Success(Return([], ctx))
    else
      var Return(v, ctx) :- InterpExpr(es[0], env, ctx);
      var Return(vs, ctx) :- InterpExprs(es[1..], env, ctx);
      Success(Return([v] + vs, ctx))
  }

  function method {:opaque} InterpLiteral(a: Exprs.Literal) : (v: Value)
    ensures HasEqValue(v)
  {
    match a
      case LitUnit => V.Unit
      case LitBool(b: bool) => V.Bool(b)
      case LitInt(i: int) => V.Int(i)
      case LitReal(r: real) => V.Real(r)
      case LitChar(c: char) => V.Char(c)
      case LitString(s: string, verbatim: bool) =>
        var chars := seq(|s|, i requires 0 <= i < |s| => V.Char(s[i]));
        assert forall c | c in chars :: WellFormedValue(c);
        assert forall c | c in chars :: HasEqValue(c);
        V.Seq(chars)
  }

  // This function is provided for convenience, and actually not used by ``InterpExpr``; for
  // detailed explanations, see the comments for ``InterpBlock``
  function method {:opaque} InterpLazy(e: Expr, env: Environment, ctx: State)
    : InterpResult<Value>
    requires e.Apply? && e.aop.Lazy?
  {
    reveal SupportsInterp();
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
    var Return(v0, ctx0) :- InterpExpr(e0, env, ctx);
    :- NeedType(e0, v0, Type.Bool);
    match (op, v0)
      case (And, Bool(false)) => Success(Return(V.Bool(false), ctx0))
      case (Or,  Bool(true))  => Success(Return(V.Bool(true), ctx0))
      case (Imp, Bool(false)) => Success(Return(V.Bool(true), ctx0))
      case (_,   Bool(b)) =>
        assert op in {Exprs.And, Exprs.Or, Exprs.Imp};
        var Return(v1, ctx1) :- InterpExpr(e1, env, ctx0);
        :- NeedType(e1, v1, Type.Bool);
        Success(Return(v1, ctx1))
  }

  // Alternate implementation of ``InterpLazy``: less efficient but more closely
  // matching intuition.
  function {:opaque} InterpLazy_Eagerly(e: Expr, env: Environment, ctx: State)
    : InterpResult<Value>
    requires e.Apply? && e.aop.Lazy? && SupportsInterp(e)
    decreases env.fuel, e, 0
  {
    reveal SupportsInterp();
    Predicates.Deep.AllImpliesChildren(e, SupportsInterp1);
    var op, e0, e1 := e.aop.lOp, e.args[0], e.args[1];
    var Return(v0, ctx0) :- InterpExpr(e0, env, ctx);
    :- NeedType(e0, v0, Type.Bool);
    var Return(v1, ctx1) :- InterpExpr(e1, env, ctx0);
    :- NeedType(e1, v1, Type.Bool);
    match (op, v0, v1)
      case (And, Bool(b0), Bool(b1)) =>
        Success(Return(V.Bool(b0 && b1), if b0 then ctx1 else ctx0))
      case (Or,  Bool(b0), Bool(b1)) =>
        Success(Return(V.Bool(b0 || b1), if b0 then ctx0 else ctx1))
      case (Imp, Bool(b0), Bool(b1)) =>
        Success(Return(V.Bool(b0 ==> b1), if b0 then ctx1 else ctx0))
  }

  lemma InterpLazy_Complete(e: Expr, env: Environment, ctx: State)
    requires e.Apply? && e.aop.Lazy?
    requires InterpLazy(e, env, ctx).Failure?
    ensures InterpLazy_Eagerly(e, env, ctx) == InterpLazy(e, env, ctx)
  {
    reveal SupportsInterp();
    reveal InterpLazy();
    reveal InterpLazy_Eagerly();
  }

  lemma InterpLazy_Eagerly_Sound(e: Expr, env: Environment, ctx: State)
    requires e.Apply? && e.aop.Lazy?
    requires InterpLazy_Eagerly(e, env, ctx).Success?
    ensures InterpLazy_Eagerly(e, env, ctx) == InterpLazy(e, env, ctx)
  {
    reveal SupportsInterp();
    reveal InterpLazy();
    reveal InterpLazy_Eagerly();
  }

  // This function is provided for convenience, and actually not used by ``InterpExpr``; for
  // detailed explanations, see the comments for ``InterpBlock``
  function method {:opaque} InterpBind(e: Expr, env: Environment, ctx: State)
    : InterpResult<Value>
    requires e.Bind?
  {
    reveal SupportsInterp();
    var Bind(bvars, vals, body) := e;
    var vars := VarsToNames(bvars);
    // A bind acts like a scope containing variable declarations:
    // - Open a scope
    var ctx1 := StartScope(ctx);
    // - Evaluate the rhs
    var Return(vals, ctx2) :- InterpExprs(vals, env, ctx1);
    // - Save the shadowed variables to the rollback
    var ctx3 := SaveToRollback(ctx2, vars);
    // - Augment the context with the new bindings
    var ctx4 := ctx3.(locals := AugmentContext(ctx3.locals, vars, vals));
    // - Execute the body
    var Return(v, ctx5) :- InterpExpr(body, env, ctx4);
    // - End the scope
    var ctx6 := EndScope(ctx, ctx5);
    // Return
    Success(Return(v, ctx6))
  }

  function method {:opaque} InterpUnaryOp(expr: Expr, op: Syntax.UnaryOp, v0: Value)
    : PureInterpResult<Value>
    requires !op.MemberSelect?
  {
    match op
      case BVNot => :- Need(v0.BitVector?, Invalid(expr));
        Success(V.BitVector(v0.width, Math.IntPow(2, v0.width) - 1 - v0.value))
      case BoolNot => :- Need(v0.Bool?, Invalid(expr));
        Success(V.Bool(!v0.b))
      case SeqLength => :- Need(v0.Seq?, Invalid(expr));
        Success(V.Int(|v0.sq|))
      case SetCard => :- Need(v0.Set?, Invalid(expr));
        Success(V.Int(|v0.st|))
      case MultisetCard => :- Need(v0.Multiset?, Invalid(expr));
        Success(V.Int(|v0.ms|))
      case MapCard => :- Need(v0.Map?, Invalid(expr));
        Success(V.Int(|v0.m|))
  }

  function method {:opaque} InterpBinaryOp(expr: Expr, bop: Syntax.BinaryOp, v0: Value, v1: Value)
    : PureInterpResult<Value>
    requires !bop.BV? && !bop.Datatypes?
  {
    match bop
      case Numeric(op) => InterpBinaryNumeric(expr, op, v0, v1)
      case Logical(op) => InterpBinaryLogical(expr, op, v0, v1)
      case Eq(op) => // FIXME which types is this Eq applicable to (vs. the type-specific ones?)
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(HasEqValue(v1), Invalid(expr));
        match op {
          case EqCommon() => Success(V.Bool(v0 == v1))
          case NeqCommon() => Success(V.Bool(v0 != v1))
        }
      // case BV(op) =>
      case Char(op) => InterpBinaryChar(expr, op, v0, v1)
      case Sets(op) => InterpBinarySets(expr, op, v0, v1)
      case Multisets(op) => InterpBinaryMultisets(expr, op, v0, v1)
      case Sequences(op) => InterpBinarySequences(expr, op, v0, v1)
      case Maps(op) => InterpBinaryMaps(expr, op, v0, v1)
      // case Datatypes(op) =>
  }

  function method InterpBinaryNumeric(expr: Expr, op: Exprs.BinaryOps.Numeric, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    match (v0, v1) {
      // Separate functions to more easily check exhaustiveness
      case (Int(x1), Int(x2)) => InterpBinaryInt(expr, op, x1, x2)
      case (Char(x1), Char(x2)) => InterpBinaryNumericChar(expr, op, x1, x2)
      case (Real(x1), Real(x2)) => InterpBinaryReal(expr, op, x1, x2)
      case _ => Failure(Invalid(expr)) // FIXME: Wf
    }
  }

  function method CheckDivisionByZero(b: bool) : Outcome<InterpError> {
    if b then Fail(DivisionByZero) else Pass
  }

  function method InterpBinaryInt(expr: Expr, bop: Syntax.BinaryOps.Numeric, x1: int, x2: int)
    : PureInterpResult<Value>
  {
    match bop {
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => Success(V.Int(x1 + x2))
      case Sub() => Success(V.Int(x1 - x2))
      case Mul() => Success(V.Int(x1 * x2))
      case Div() => :- CheckDivisionByZero(x2 == 0); Success(V.Int(x1 / x2))
      case Mod() => :- CheckDivisionByZero(x2 == 0); Success(V.Int(x1 % x2))
    }
  }

  function method NeedIntBounds(x: int, low: int, high: int) : PureInterpResult<int> {
    :- Need(low <= x < high, OutOfIntBounds(x, Some(low), Some(high)));
    Success(x)
  }

  function method InterpBinaryNumericChar(expr: Expr, bop: Syntax.BinaryOps.Numeric, x1: char, x2: char)
    : PureInterpResult<Value>
  {
    match bop { // FIXME: These first four cases are not used (see InterpBinaryChar instead)
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => var x :- NeedIntBounds(x1 as int + x2 as int, 0, 256); Success(V.Char(x as char))
      case Sub() => var x :- NeedIntBounds(x1 as int - x2 as int, 0, 256); Success(V.Char(x as char))
      case Mul() => Failure(Invalid(expr))
      case Div() => Failure(Invalid(expr))
      case Mod() => Failure(Invalid(expr))
    }
  }

  function method InterpBinaryReal(expr: Expr, bop: Syntax.BinaryOps.Numeric, x1: real, x2: real)
    : PureInterpResult<Value>
  {
    match bop {
      case Lt() => Success(V.Bool(x1 < x2))
      case Le() => Success(V.Bool(x1 <= x2))
      case Ge() => Success(V.Bool(x1 >= x2))
      case Gt() => Success(V.Bool(x1 > x2))
      case Add() => Success(V.Real(x1 + x2))
      case Sub() => Success(V.Real(x1 - x2))
      case Mul() => Success(V.Real(x1 * x2))
      case Div() => :- CheckDivisionByZero(x2 == 0 as real); Success(V.Real(x1 / x2))
      case Mod() => Failure(Invalid(expr))
    }
  }

  function method InterpBinaryLogical(expr: Expr, op: Exprs.BinaryOps.Logical, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    :- Need(v0.Bool? && v1.Bool?, Invalid(expr));
    match op
      case Iff() =>
        Success(V.Bool(v0.b <==> v1.b))
  }

  function method InterpBinaryChar(expr: Expr, op: Syntax.BinaryOps.Char, v0: Value, v1: Value)
    : PureInterpResult<Value>
  { // FIXME eliminate distinction between GtChar and GT?
    :- Need(v0.Char? && v1.Char?, Invalid(expr));
    match op
      case LtChar() =>
        Success(V.Bool(v0.c < v1.c))
      case LeChar() =>
        Success(V.Bool(v0.c <= v1.c))
      case GeChar() =>
        Success(V.Bool(v0.c >= v1.c))
      case GtChar() =>
        Success(V.Bool(v0.c > v1.c))
  }

  function method InterpBinarySets(expr: Expr, op: Exprs.BinaryOps.Sets, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    // Rk.: we enforce through `WellFormedEqValue` that sets contain values with a decidable
    // equality.
    match op
      case SetEq() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st == v1.st))
      case SetNeq() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st != v1.st))
      case Subset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st <= v1.st))
      case Superset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st >= v1.st))
      case ProperSubset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st < v1.st))
      case ProperSuperset() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st > v1.st))
      case Disjoint() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Bool(v0.st !! v1.st))
      case Union() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Set(v0.st + v1.st))
      case Intersection() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Set(v0.st * v1.st))
      case SetDifference() => :- Need(v0.Set? && v1.Set?, Invalid(expr));
        Success(V.Set(v0.st - v1.st))
      case InSet() =>
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(v1.Set?, Invalid(expr));
        Success(V.Bool(v0 in v1.st))
      case NotInSet() =>
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(v1.Set?, Invalid(expr));
        Success(V.Bool(v0 !in v1.st))
  }

  function method InterpBinaryMultisets(expr: Expr, op: Exprs.BinaryOps.Multisets, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    // Rk.: we enforce through `WellFormedEqValue` that multisets contain values with a decidable
    // equality.
    match op // DISCUSS
      case MultisetEq() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms == v1.ms))
      case MultisetNeq() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms != v1.ms))
      case MultiSubset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms <= v1.ms))
      case MultiSuperset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms >= v1.ms))
      case ProperMultiSubset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms < v1.ms))
      case ProperMultiSuperset() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms > v1.ms))
      case MultisetDisjoint() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0.ms !! v1.ms))
      case MultisetUnion() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Multiset(v0.ms + v1.ms))
      case MultisetIntersection() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Multiset(v0.ms * v1.ms))
      case MultisetDifference() => :- Need(v0.Multiset? && v1.Multiset?, Invalid(expr));
        Success(V.Multiset(v0.ms - v1.ms))
      case InMultiset() =>
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0 in v1.ms))
      case NotInMultiset() =>
        :- Need(HasEqValue(v0), Invalid(expr));
        :- Need(v1.Multiset?, Invalid(expr));
        Success(V.Bool(v0 !in v1.ms))
      case MultisetSelect() =>
        :- Need(HasEqValue(v1), Invalid(expr));
        :- Need(v0.Multiset?, Invalid(expr));
        Success(V.Int(v0.ms[v1]))
  }

  function method InterpBinarySequences(expr: Expr, op: Exprs.BinaryOps.Sequences, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    // Rk.: sequences don't necessarily contain values with decidable equality, we
    // thus dynamically check that we have what we need depending on the operation
    // we want to perform.
    // TODO: the dynamic checks for decidable equality may make the interpreter quite
    // slow. We might want to deduce this from a type check instead.
    match op
      case SeqEq() =>
        :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.sq == v1.sq))
      case SeqNeq() =>
        :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.sq != v1.sq))
      case Prefix() =>
        :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.sq <= v1.sq))
      case ProperPrefix() =>
        :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.sq < v1.sq))
      case Concat() => :- Need(v0.Seq? && v1.Seq?, Invalid(expr));
        Success(V.Seq(v0.sq + v1.sq))
      case InSeq() =>
        :- Need(v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0 in v1.sq))
      case NotInSeq() =>
        :- Need(v1.Seq?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0 !in v1.sq))
      case SeqDrop() =>
        :- NeedValidEndpoint(expr, v0, v1);
        Success(V.Seq(v0.sq[v1.i..]))
      case SeqTake() =>
        :- NeedValidEndpoint(expr, v0, v1);
        Success(V.Seq(v0.sq[..v1.i]))
      case SeqSelect() =>
        :- NeedValidIndex(expr, v0, v1);
        Success(v0.sq[v1.i])
  }

  function method InterpBinaryMaps(expr: Expr, op: Exprs.BinaryOps.Maps, v0: Value, v1: Value)
    : PureInterpResult<Value>
  {
    // Rk.: values in maps don't necessarily have a decidable equality. We thus perform
    // dynamic checks when we need one and fail if it is not the case.
    match op
      case MapEq() =>
        :- Need(v0.Map? && v1.Map?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.m == v1.m))
      case MapNeq() =>
        :- Need(v0.Map? && v1.Map?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0.m != v1.m))
      case MapMerge() =>
        :- Need(v0.Map? && v1.Map?, Invalid(expr));
        Success(V.Map(v0.m + v1.m))
      case MapSubtraction() =>
        :- Need(v0.Map? && v1.Set?, Invalid(expr));
        Success(V.Map(v0.m - v1.st))
      case InMap() =>
        :- Need(v1.Map?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0 in v1.m))
      case NotInMap() =>
        :- Need(v1.Map?, Invalid(expr));
        :- Need(HasEqValue(v0), Invalid(expr)); // We need decidable equality
        Success(V.Bool(v0 !in v1.m))
      case MapSelect() =>
        :- Need(v0.Map?, Invalid(expr));
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        :- Need(v1 in v0.m, OutOfMapDomain(v0, v1));
        Success(v0.m[v1])
  }

  function method {:opaque} InterpTernaryOp(expr: Expr, top: Syntax.TernaryOp, v0: Value, v1: Value, v2: Value)
    : PureInterpResult<Value>
  {
    match top
      case Sequences(op) =>
        InterpTernarySequences(expr, op, v0, v1, v2)
      case Multisets(op) =>
        InterpTernaryMultisets(expr, op, v0, v1, v2)
      case Maps(op) =>
        InterpTernaryMaps(expr, op, v0, v1, v2)
  }

  function method NeedValidIndex(expr: Expr, vs: Value, vidx: Value)
    : Outcome<InterpError>
  { // FIXME no monadic operator for combining outcomes?
    match Need(vidx.Int? && vs.Seq?, Invalid(expr))
      case Pass() => Need(0 <= vidx.i < |vs.sq|, OutOfSeqBounds(vs, vidx))
      case fail => fail
  }

  function method NeedValidEndpoint(expr: Expr, vs: Value, vidx: Value)
    : Outcome<InterpError>
  {
    match Need(vidx.Int? && vs.Seq?, Invalid(expr))
      case Pass() => Need(0 <= vidx.i <= |vs.sq|, OutOfSeqBounds(vs, vidx))
      case fail => fail
  }

  function method InterpTernarySequences(expr: Expr, op: Syntax.TernaryOps.Sequences, v0: Value, v1: Value, v2: Value)
    : PureInterpResult<Value>
  {
    match op
      case SeqUpdate() =>
        :- NeedValidIndex(expr, v0, v1);
        Success(V.Seq(v0.sq[v1.i := v2]))
      case SeqSubseq() =>
        :- NeedValidEndpoint(expr, v0, v2);
        :- Need(v1.Int?, Invalid(expr));
        :- Need(0 <= v1.i <= v2.i, OutOfIntBounds(v1.i, Some(0), Some(v2.i)));
        Success(V.Seq(v0.sq[v1.i..v2.i]))
  }

  function method InterpTernaryMultisets(expr: Expr, op: Syntax.TernaryOps.Multisets, v0: Value, v1: Value, v2: Value)
    : PureInterpResult<Value>
  {
    match op
      case MultisetUpdate() =>
        :- Need(v0.Multiset?, Invalid(expr));
        :- Need(v2.Int? && v2.i >= 0, Invalid(expr));
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Multiset(v0.ms[v1 := v2.i]))
  }

  function method InterpTernaryMaps(expr: Expr, op: Syntax.TernaryOps.Maps, v0: Value, v1: Value, v2: Value)
    : PureInterpResult<Value>
  {
    match op
      case MapUpdate() =>
        :- Need(v0.Map?, Invalid(expr));
        :- Need(HasEqValue(v1), Invalid(expr)); // We need decidable equality
        Success(V.Map(v0.m[v1 := v2]))
  }

  function method {:opaque} InterpDisplay(e: Expr, kind: Types.CollectionKind, argvs: seq<Value>)
    : PureInterpResult<Value>
  {
    match kind
      case Map(_) =>
        var m :- InterpMapDisplay(e, argvs);
        Success(V.Map(m))
      case Multiset() =>
        :- Need(forall i | 0 <= i < |argvs| :: HasEqValue(argvs[i]), Invalid(e)); // The elements must have a decidable equality
        var v := V.Multiset(multiset(argvs));
        assert WellFormedEqValue(v); // Doesn't work without this assert
        Success(v)
      case Seq() =>
        Success(V.Seq(argvs))
      case Set() =>
        :- Need(forall x | x in argvs :: HasEqValue(x), Invalid(e)); // The elements must have a decidable equality
        Success(V.Set(set s | s in argvs))
  }

  function method InterpMapDisplay(e: Expr, argvs: seq<Value>)
    : PureInterpResult<map<EqWV, Value>>
  {
    var pairs :- Seq.MapResult(argvs, argv => PairOfMapDisplaySeq(e, argv));
    Success(MapOfPairs(pairs))
  }

  function method PairOfMapDisplaySeq(e: Expr, argv: Value)
    : PureInterpResult<(EqWV, Value)>
  {
    :- Need(argv.Seq? && |argv.sq| == 2, Invalid(e));
    :- Need(HasEqValue(argv.sq[0]), Invalid(e));
    Success((argv.sq[0], argv.sq[1]))
  }

  function method AugmentContext(base: Context, vars: seq<string>, vals: seq<Value>)
    : Context
    requires |vars| == |vals|
  {
    base + MapOfPairs(Seq.Zip(vars, vals))
  }

  function method {:opaque} BuildCallState(base: Context, vars: seq<string>, vals: seq<Value>)
    : State
    requires |vars| == |vals|
  {
    State(locals := AugmentContext(base, vars, vals))
  }

  function method {:opaque} InterpFunctionCall(e: Expr, env: Environment, fn: Value, argvs: seq<Value>)
    : PureInterpResult<Value>
    decreases env.fuel, e, 0
  {
    :- Need(env.fuel > 0, OutOfFuel(fn));
    :- Need(fn.Closure?, Invalid(e));
    reveal SupportsInterp();
    Predicates.Deep.AllImpliesChildren(fn.body, SupportsInterp1);
    :- Need(|fn.vars| == |argvs|, SignatureMismatch(fn.vars, argvs));
    var ctx := State(locals := AugmentContext(fn.ctx, fn.vars, argvs));
    var Return(val, ctx) :- InterpExpr(fn.body, env.(fuel := env.fuel - 1), ctx);
    Success(val)
  }

  // TODO(SMH): update this to not enforce the intermediary blocks to evaluate to `Unit`,
  // and use ``InterpExprs``. We will add a condition on ``Expr`` stating that there can't
  // be empty blocks, and will use `{ () }` as a placeholder for an empty block whenever
  // we need to use one.
  // DISCUSS: another possibility is to do as follows:
  // - ``Block`` takes one single expression, controls a scope and always evaluates to unit
  // - have an equivalent of the Lisp progn
  // - keep ``Bind``
  function method {:opaque} InterpBlock_Exprs(es: seq<Expr>, env: Environment, ctx: State)
    : (r: InterpResult<Value>)
    decreases env.fuel, es, 0
  {
    // There is something subtle here:
    // - if a block is empty, it evaluates to `Unit`
    // - otherwise, it evaluates to the value of the last expression in the block (after all
    //   the previous expressions have been evaluated, of course)
    if es == [] then Success(Return(V.Unit, ctx))
    else if |es| == 1 then
      InterpExpr(es[0], env, ctx)
    else
      // Evaluate the first expression
      var Return(val, ctx) :- InterpExpr(es[0], env, ctx);
      :- NeedType(es[0], val, Types.Unit);
      // Evaluate the remaining expressions
      InterpBlock_Exprs(es[1..], env, ctx)
  }

  // TODO: maybe it doesn't make sense anymore for this function to be opaque?
  function method {:opaque} InterpBlock(stmts: seq<Expr>, env: Environment, ctx: State)
    : (r: InterpResult<Value>)
    // This function is a utility function and is not used by the interpreter itself to avoid
    // unfolding issues linked to the fuel. See the comment in the ``Block`` case of ``InterpExpr``
    // for more explanations.
  {
    var ctx1 := StartScope(ctx);
    var Return(v, ctx2) :- InterpBlock_Exprs(stmts, env, ctx1);
    var ctx3 := EndScope(ctx, ctx2);
    Success(Return(v, ctx3))
  }

  function method {:opaque} SaveToRollback(ctx: State, vars: seq<string>)
    : State
    // This function is used when evaluating variable declarations:
    // - save the non-local variables which are about to be shadowed into the rollback context
    // - set the declared variables as "uninitialized" (by removing them from the local
    //   context)
  {
    // Convert the sequence of variables to a set
    var vars := set x | x in vars;
    // We have to save the variables which:
    // - are already present in the context (with a value)
    // - are not in rollback
    var save := map x | x in (vars * ctx.locals.Keys) - ctx.rollback.Keys :: ctx.locals[x];
    // Update the contexts
    ctx.(locals := ctx.locals - vars, rollback := ctx.rollback + save)
  }

/*  function method InterpBind(e: Expr, env: Environment, ctx: State, vars: seq<string>, vals: seq<Value>, body: Expr)
    : InterpResult<Value>
    requires body < e
    requires |vars| == |vals|
    decreases env.fuel, e, 0
  {
    var bodyCtx := ctx.(locals := AugmentContext(ctx.locals, vars, vals));
    var Return(val, bodyCtx) :- InterpExpr(body, env, bodyCtx);
    var ctx := ctx.(locals := ctx.locals + (bodyCtx.locals - set v | v in vars)); // Preserve mutation
    Success(Return(val, ctx))
  }*/

  function method {:opaque} InterpExprs_Block(es: seq<Expr>, env: Environment, ctx: State)
    : (r: InterpResult<Value>)
    // Alternative definition for ``InterpBlock_Exprs`` based on ``InterpExprs``, and which we use
    // for reasoning purposes. When it fails, it doesn't return the same error as ``InterpBlock_Exprs``,
    // but this is often not an issue and allows to factorize the proofs.
  {
    var ctx0 := ctx;
    // Evaluate all the statements
    var Return(vs, ctx) :- InterpExprs(es, env, ctx);
    // Case disjunction: the block is empty or not
    if es == [] then Success(Return(V.Unit, ctx))
    else
      // Check that all the statements but the last one evaluate to unit
      reveal SupportsInterp();
      :- Need(Seq.All((v: Value) => v.HasType(Types.Unit), vs[0..(|vs|-1)]), Invalid(Exprs.Block(es))); // TODO(SMH): TypeError requires a value...
      // Return the value the last statement evaluated to
      Success(Return(vs[|vs| - 1], ctx))
  }

  function method StartScope(ctx: State): State {
    ctx.(rollback := map [])
  }

  function method EndScope(ctx: State, ctx1: State): State {
    // It is important to rollback *then* restrict the map.
    // Ex.:
    // ```
    // // locals: [], rollback: []
    // var y := 0;
    // // locals: [y -> 0], rollback: []
    // {
    //   var x := 0;
    //   // locals: [x -> 0, y -> 0], rollback: []
    //   var x := true; // Redeclaring `x`: forbidden by Dafny, allowed by our semantics
    //   // locals: [x -> true, y -> 0], rollback: [x -> 0]
    // }
    // // If we restrict *then* rollback, we leak `x`
    // ```
    var locals := (ctx1.locals + ctx1.rollback);
    // Below: we should actually have the invariant that `locals` is included in `ctx.locals`, but
    // we don't 
    var locals1 := map x | x in (locals.Keys * ctx.locals.Keys) :: locals[x];
    State(locals := locals1, rollback := ctx.rollback)
  }

  // This lemma is here for sanity purposes - see the comment for the ``Block`` case in ``InterpExpr``
  lemma InterpBlock_Correct(e: Expr, env: Environment, ctx: State)
    requires e.Block?
    ensures reveal SupportsInterp(); InterpBlock(e.stmts, env, ctx) == InterpExpr(e, env, ctx)
  {
    reveal InterpExpr();
    reveal InterpBlock();
  }

  // This lemma is here for sanity purposes - see the comment for the ``Lazy`` case in ``InterpExpr``
  lemma InterpLazy_Correct(e: Expr, env: Environment, ctx: State)
    requires e.Apply? && e.aop.Lazy?
    ensures InterpExpr(e, env, ctx) == InterpLazy(e, env, ctx)
  {
    reveal InterpExpr();
    reveal InterpLazy();
  }

  // This lemma is here for sanity purposes - see the comment for the ``Bind`` case in ``InterpExpr``
  lemma InterpBind_Correct(e: Expr, env: Environment, ctx: State)
    requires e.Bind?
    ensures InterpExpr(e, env, ctx) == InterpBind(e, env, ctx)
  {
    reveal InterpExpr();
    reveal InterpBind();
  }
}

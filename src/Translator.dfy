include "CSharpDafnyASTModel.dfy"
include "CSharpInterop.dfy"
include "CSharpDafnyInterop.dfy"
include "CSharpDafnyASTInterop.dfy"
include "Library.dfy"
include "AST.dfy"
include "Predicates.dfy"

module DafnyCompilerCommon.Translator {
  import opened Lib
  import opened Lib.Datatypes
  import opened CSharpInterop
  import opened CSharpInterop.System
  import opened CSharpDafnyInterop
  import opened CSharpDafnyInterop.Microsoft
  import opened CSharpDafnyASTInterop
  import C = CSharpDafnyASTModel
  import D = AST
  import DE = AST.Exprs
  import DT = AST.Types
  import P = Predicates.Deep

  datatype TranslationError =
    | Invalid(msg: string)
    | GhostExpr(expr: C.Expression)
    | UnsupportedType(ty: C.Type)
    | UnsupportedExpr(expr: C.Expression)
    | UnsupportedStmt(stmt: C.Statement)
    | UnsupportedMember(decl: C.MemberDecl)
  {
    function method ToString() : string {
      match this
        case Invalid(msg) =>
          "Invalid term: " + msg
        case GhostExpr(expr) =>
          "Ghost expression: " + TypeConv.ObjectToString(expr)
        case UnsupportedType(ty) =>
          "Unsupported type: " + TypeConv.ObjectToString(ty)
        case UnsupportedExpr(expr) =>
          "Unsupported expression: " + TypeConv.ObjectToString(expr)
        case UnsupportedStmt(stmt) =>
          "Unsupported statement: " + TypeConv.ObjectToString(stmt)
        case UnsupportedMember(decl) =>
          "Unsupported declaration: " + TypeConv.ObjectToString(decl)
    }
  }

  type Expr = e: DE.Expr | P.All_Expr(e, DE.WellFormed)
    witness DE.Block([])

  type TranslationResult<+A> =
    Result<A, TranslationError>

  function method TranslateType(ty: C.Type)
    : TranslationResult<DT.Type>
    reads *
    decreases TypeHeight(ty)
  {
    var ty := TypeUtils.NormalizeExpand(ty);
    if ty is C.BoolType then
      Success(DT.Bool)
    else if ty is C.CharType then
      Success(DT.Char)
    else if ty is C.IntType then
      Success(DT.Int)
    else if ty is C.RealType then
      Success(DT.Real)
    else if ty is C.BigOrdinalType then
      Success(DT.BigOrdinal)
    else if ty is C.BitvectorType then
      var bvTy := ty as C.BitvectorType;
      :- Need(bvTy.Width >= 0, Invalid("BV width must be >= 0"));
      Success(DT.BitVector(bvTy.Width as int))
    // TODO: the following could be simplified
    else if ty is C.MapType then
      var ty := ty as C.MapType;
      assume TypeHeight(ty.Domain) < TypeHeight(ty);
      assume TypeHeight(ty.Range) < TypeHeight(ty);
      var domainTy :- TranslateType(ty.Domain);
      var rangeTy :- TranslateType(ty.Range);
      Success(DT.Collection(ty.Finite, DT.CollectionKind.Map(domainTy), rangeTy))
    else if ty is C.SetType then
      var ty := ty as C.SetType;
      assume TypeHeight(ty.Arg) < TypeHeight(ty);
      var eltTy :- TranslateType(ty.Arg);
      Success(DT.Collection(ty.Finite, DT.CollectionKind.Set, eltTy))
    else if ty is C.MultiSetType then
      var ty := ty as C.MultiSetType;
      assume TypeHeight(ty.Arg) < TypeHeight(ty);
      var eltTy :- TranslateType(ty.Arg);
      Success(DT.Collection(true, DT.CollectionKind.Multiset, eltTy))
    else if ty is C.SeqType then
      var ty := ty as C.SeqType;
      assume TypeHeight(ty.Arg) < TypeHeight(ty);
      var eltTy :- TranslateType(ty.Arg);
      Success(DT.Collection(true, DT.CollectionKind.Seq, eltTy))
    else
      Failure(UnsupportedType(ty))
  }

  const GhostUnaryOps: set<C.UnaryOpExpr__ResolvedOpcode> :=
    {C.UnaryOpExpr__ResolvedOpcode.Fresh,
     C.UnaryOpExpr__ResolvedOpcode.Allocated,
     C.UnaryOpExpr__ResolvedOpcode.Lit}

  const UnaryOpMap: map<C.UnaryOpExpr__ResolvedOpcode, D.UnaryOp> :=
    map[C.UnaryOpExpr__ResolvedOpcode.BVNot := D.UnaryOps.BVNot,
        C.UnaryOpExpr__ResolvedOpcode.BoolNot := D.UnaryOps.BoolNot,
        C.UnaryOpExpr__ResolvedOpcode.SeqLength := D.UnaryOps.SeqLength,
        C.UnaryOpExpr__ResolvedOpcode.SetCard := D.UnaryOps.SetCard,
        C.UnaryOpExpr__ResolvedOpcode.MultiSetCard := D.UnaryOps.MultisetCard,
        C.UnaryOpExpr__ResolvedOpcode.MapCard := D.UnaryOps.MapCard]

  const LazyBinopMap: map<C.BinaryExpr__ResolvedOpcode, DE.LazyOp> :=
    map[C.BinaryExpr__ResolvedOpcode.Imp := DE.Imp,
        C.BinaryExpr__ResolvedOpcode.And := DE.And,
        C.BinaryExpr__ResolvedOpcode.Or := DE.Or]

  const EagerBinopMap: map<C.BinaryExpr__ResolvedOpcode, DE.BinaryOps.T> :=
    map[C.BinaryExpr__ResolvedOpcode.Iff := D.BinaryOps.Logical(D.BinaryOps.Iff),
        C.BinaryExpr__ResolvedOpcode.EqCommon := D.BinaryOps.Eq(D.BinaryOps.EqCommon),
        C.BinaryExpr__ResolvedOpcode.NeqCommon := D.BinaryOps.Eq(D.BinaryOps.NeqCommon),
        C.BinaryExpr__ResolvedOpcode.Lt := D.BinaryOps.Numeric(D.BinaryOps.Lt),
        C.BinaryExpr__ResolvedOpcode.Le := D.BinaryOps.Numeric(D.BinaryOps.Le),
        C.BinaryExpr__ResolvedOpcode.Ge := D.BinaryOps.Numeric(D.BinaryOps.Ge),
        C.BinaryExpr__ResolvedOpcode.Gt := D.BinaryOps.Numeric(D.BinaryOps.Gt),
        C.BinaryExpr__ResolvedOpcode.Add := D.BinaryOps.Numeric(D.BinaryOps.Add),
        C.BinaryExpr__ResolvedOpcode.Sub := D.BinaryOps.Numeric(D.BinaryOps.Sub),
        C.BinaryExpr__ResolvedOpcode.Mul := D.BinaryOps.Numeric(D.BinaryOps.Mul),
        C.BinaryExpr__ResolvedOpcode.Div := D.BinaryOps.Numeric(D.BinaryOps.Div),
        C.BinaryExpr__ResolvedOpcode.Mod := D.BinaryOps.Numeric(D.BinaryOps.Mod),
        C.BinaryExpr__ResolvedOpcode.LeftShift := D.BinaryOps.BV(D.BinaryOps.LeftShift),
        C.BinaryExpr__ResolvedOpcode.RightShift := D.BinaryOps.BV(D.BinaryOps.RightShift),
        C.BinaryExpr__ResolvedOpcode.BitwiseAnd := D.BinaryOps.BV(D.BinaryOps.BitwiseAnd),
        C.BinaryExpr__ResolvedOpcode.BitwiseOr := D.BinaryOps.BV(D.BinaryOps.BitwiseOr),
        C.BinaryExpr__ResolvedOpcode.BitwiseXor := D.BinaryOps.BV(D.BinaryOps.BitwiseXor),
        C.BinaryExpr__ResolvedOpcode.LtChar := D.BinaryOps.Char(D.BinaryOps.LtChar),
        C.BinaryExpr__ResolvedOpcode.LeChar := D.BinaryOps.Char(D.BinaryOps.LeChar),
        C.BinaryExpr__ResolvedOpcode.GeChar := D.BinaryOps.Char(D.BinaryOps.GeChar),
        C.BinaryExpr__ResolvedOpcode.GtChar := D.BinaryOps.Char(D.BinaryOps.GtChar),
        C.BinaryExpr__ResolvedOpcode.SeqEq := D.BinaryOps.Sequences(D.BinaryOps.SeqEq),
        C.BinaryExpr__ResolvedOpcode.SeqNeq := D.BinaryOps.Sequences(D.BinaryOps.SeqNeq),
        C.BinaryExpr__ResolvedOpcode.ProperPrefix := D.BinaryOps.Sequences(D.BinaryOps.ProperPrefix),
        C.BinaryExpr__ResolvedOpcode.Prefix := D.BinaryOps.Sequences(D.BinaryOps.Prefix),
        C.BinaryExpr__ResolvedOpcode.Concat := D.BinaryOps.Sequences(D.BinaryOps.Concat),
        C.BinaryExpr__ResolvedOpcode.InSeq := D.BinaryOps.Sequences(D.BinaryOps.InSeq),
        C.BinaryExpr__ResolvedOpcode.NotInSeq := D.BinaryOps.Sequences(D.BinaryOps.NotInSeq),
        C.BinaryExpr__ResolvedOpcode.SetEq := D.BinaryOps.Sets(D.BinaryOps.SetEq),
        C.BinaryExpr__ResolvedOpcode.SetNeq := D.BinaryOps.Sets(D.BinaryOps.SetNeq),
        C.BinaryExpr__ResolvedOpcode.ProperSubset := D.BinaryOps.Sets(D.BinaryOps.ProperSubset),
        C.BinaryExpr__ResolvedOpcode.Subset := D.BinaryOps.Sets(D.BinaryOps.Subset),
        C.BinaryExpr__ResolvedOpcode.Superset := D.BinaryOps.Sets(D.BinaryOps.Superset),
        C.BinaryExpr__ResolvedOpcode.ProperSuperset := D.BinaryOps.Sets(D.BinaryOps.ProperSuperset),
        C.BinaryExpr__ResolvedOpcode.Disjoint := D.BinaryOps.Sets(D.BinaryOps.Disjoint),
        C.BinaryExpr__ResolvedOpcode.InSet := D.BinaryOps.Sets(D.BinaryOps.InSet),
        C.BinaryExpr__ResolvedOpcode.NotInSet := D.BinaryOps.Sets(D.BinaryOps.NotInSet),
        C.BinaryExpr__ResolvedOpcode.Union := D.BinaryOps.Sets(D.BinaryOps.Union),
        C.BinaryExpr__ResolvedOpcode.Intersection := D.BinaryOps.Sets(D.BinaryOps.Intersection),
        C.BinaryExpr__ResolvedOpcode.SetDifference := D.BinaryOps.Sets(D.BinaryOps.SetDifference),
        C.BinaryExpr__ResolvedOpcode.MultiSetEq := D.BinaryOps.Multisets(D.BinaryOps.MultisetEq),
        C.BinaryExpr__ResolvedOpcode.MultiSetNeq := D.BinaryOps.Multisets(D.BinaryOps.MultisetNeq),
        C.BinaryExpr__ResolvedOpcode.MultiSubset := D.BinaryOps.Multisets(D.BinaryOps.MultiSubset),
        C.BinaryExpr__ResolvedOpcode.MultiSuperset := D.BinaryOps.Multisets(D.BinaryOps.MultiSuperset),
        C.BinaryExpr__ResolvedOpcode.ProperMultiSubset := D.BinaryOps.Multisets(D.BinaryOps.ProperMultiSubset),
        C.BinaryExpr__ResolvedOpcode.ProperMultiSuperset := D.BinaryOps.Multisets(D.BinaryOps.ProperMultiSuperset),
        C.BinaryExpr__ResolvedOpcode.MultiSetDisjoint := D.BinaryOps.Multisets(D.BinaryOps.MultisetDisjoint),
        C.BinaryExpr__ResolvedOpcode.InMultiSet := D.BinaryOps.Multisets(D.BinaryOps.InMultiset),
        C.BinaryExpr__ResolvedOpcode.NotInMultiSet := D.BinaryOps.Multisets(D.BinaryOps.NotInMultiset),
        C.BinaryExpr__ResolvedOpcode.MultiSetUnion := D.BinaryOps.Multisets(D.BinaryOps.MultisetUnion),
        C.BinaryExpr__ResolvedOpcode.MultiSetIntersection := D.BinaryOps.Multisets(D.BinaryOps.MultisetIntersection),
        C.BinaryExpr__ResolvedOpcode.MultiSetDifference := D.BinaryOps.Multisets(D.BinaryOps.MultisetDifference),
        C.BinaryExpr__ResolvedOpcode.MapEq := D.BinaryOps.Maps(D.BinaryOps.MapEq),
        C.BinaryExpr__ResolvedOpcode.MapNeq := D.BinaryOps.Maps(D.BinaryOps.MapNeq),
        C.BinaryExpr__ResolvedOpcode.InMap := D.BinaryOps.Maps(D.BinaryOps.InMap),
        C.BinaryExpr__ResolvedOpcode.NotInMap := D.BinaryOps.Maps(D.BinaryOps.NotInMap),
        C.BinaryExpr__ResolvedOpcode.MapMerge := D.BinaryOps.Maps(D.BinaryOps.MapMerge),
        C.BinaryExpr__ResolvedOpcode.MapSubtraction := D.BinaryOps.Maps(D.BinaryOps.MapSubtraction),
        C.BinaryExpr__ResolvedOpcode.RankLt := D.BinaryOps.Datatypes(D.BinaryOps.RankLt),
        C.BinaryExpr__ResolvedOpcode.RankGt := D.BinaryOps.Datatypes(D.BinaryOps.RankGt)];

  const BinaryOpCodeMap: map<C.BinaryExpr__ResolvedOpcode, DE.ApplyOp> :=
    (map k | k in LazyBinopMap  :: DE.Lazy(LazyBinopMap[k])) +
    (map k | k in EagerBinopMap :: DE.Eager(DE.BinaryOp(EagerBinopMap[k])))

  function method TranslateIdentifierExpr(ie: C.IdentifierExpr)
    : (e: TranslationResult<Expr>)
    reads *
  {
    Success(DE.Var(TypeConv.AsString(ie.Name)))
  }

  predicate Decreases(u: object, v: object)
    requires u is C.Expression || u is C.Statement
    requires v is C.Expression || v is C.Statement
  {
    ASTHeight(u) < ASTHeight(v)
  }

  function method TranslateUnary(u: C.UnaryExpr)
    : (e: TranslationResult<Expr>)
    decreases ASTHeight(u), 0
    reads *
  {
    :- Need(u is C.UnaryOpExpr, UnsupportedExpr(u));
    var u := u as C.UnaryOpExpr;
    var op, e := u.ResolvedOp, u.E;
    assume Decreases(e, u);
    :- Need(op !in GhostUnaryOps, GhostExpr(u));
    :- Need(op in UnaryOpMap.Keys, UnsupportedExpr(u));
    var te :- TranslateExpression(e);
    Success(DE.Apply(DE.Eager(DE.UnaryOp(UnaryOpMap[op])), [te]))
  }

  function method TranslateBinary(b: C.BinaryExpr)
    : (e: TranslationResult<Expr>)
    decreases ASTHeight(b), 0
    reads *
  {
    var op, e0, e1 := b.ResolvedOp, b.E0, b.E1;
    // LATER b.AccumulatesForTailRecursion
    assume Decreases(e0, b);
    assume Decreases(e1, b);
    :- Need(op in BinaryOpCodeMap, UnsupportedExpr(b));
    var t0 :- TranslateExpression(e0);
    var t1 :- TranslateExpression(e1);
    Success(DE.Apply(BinaryOpCodeMap[op], [t0, t1]))
  }

  function method TranslateLiteral(l: C.LiteralExpr)
    : (e: TranslationResult<Expr>)
    reads *
  {
    if l.Value is Boolean then
      Success(DE.Literal(DE.LitBool(TypeConv.AsBool(l.Value))))
    else if l.Value is Numerics.BigInteger then
      Success(DE.Literal(DE.LitInt(TypeConv.AsInt(l.Value))))
    else if l.Value is BaseTypes.BigDec then
      Success(DE.Literal(DE.LitReal(TypeConv.AsReal(l.Value)))) // TODO test
    else if l.Value is String then
      var str := TypeConv.AsString(l.Value);
      if l is C.CharLiteralExpr then
        :- Need(|str| == 1, Invalid("CharLiteralExpr must contain a single character."));
        Success(DE.Literal(DE.LitChar(str[0])))
      else if l is C.StringLiteralExpr then
        var sl := l as C.StringLiteralExpr;
        Success(DE.Literal(DE.LitString(str, sl.IsVerbatim)))
      else
        Failure(Invalid("LiteralExpr with .Value of type string must be a char or a string."))
    else
      Failure(UnsupportedExpr(l))
  }

  function method TranslateApplyExpr(ae: C.ApplyExpr)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(ae), 0
  {
    assume Decreases(ae.Function, ae);
    var fn :- TranslateExpression(ae.Function);
    var args := ListUtils.ToSeq(ae.Args);
    var args :- Seq.MapResult(args, e requires e in args reads * =>
      assume Decreases(e, ae); TranslateExpression(e));
    Success(DE.Apply(DE.Eager(DE.FunctionCall()), [fn] + args))
  }

  function method TranslateMemberSelect(obj: C.Expression, fullName: System.String)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(obj), 3
  {
    var fname := TypeConv.AsString(fullName);
    if obj.Resolved is C.StaticReceiverExpr then
      Success(DE.Var(fname))
    else
      var obj :- TranslateExpression(obj);
      Success(DE.Apply(DE.Eager(DE.UnaryOp(DE.UnaryOps.MemberSelect(fname))), [obj]))
  }

  function method TranslateMemberSelectExpr(me: C.MemberSelectExpr)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(me), 0
  {
    assume Decreases(me.Obj, me);
    TranslateMemberSelect(me.Obj, me.Member.FullName)
  }

  function method TranslateFunctionCallExpr(fce: C.FunctionCallExpr)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(fce), 0
  {
    assume Decreases(fce.Receiver, fce);
    var fn :- TranslateMemberSelect(fce.Receiver, fce.Function.FullName);
    var args := ListUtils.ToSeq(fce.Args);
    var args :- Seq.MapResult(args, e requires e in args reads * =>
      assume Decreases(e, fce); TranslateExpression(e));
    Success(DE.Apply(DE.Eager(DE.FunctionCall()), [fn] + args))
  }

  function method TranslateDatatypeValue(dtv: C.DatatypeValue)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(dtv), 0
  {
    var ctor := dtv.Ctor;
    var n := TypeConv.AsString(ctor.Name);
    var typeArgs :- Seq.MapResult(ListUtils.ToSeq(dtv.InferredTypeArgs), TranslateType);
    // TODO: also include formals in the following, and filter out ghost arguments
    var args := ListUtils.ToSeq(dtv.Arguments);
    var args :- Seq.MapResult(args, e requires e in args reads * =>
      assume Decreases(e, dtv); TranslateExpression(e));
    Success(DE.Apply(DE.Eager(DE.DataConstructor([n], typeArgs)), args)) // TODO: proper path
  }

  function method TranslateDisplayExpr(de: C.DisplayExpression)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(de), 0
  {
    var ty :- TranslateType(de.Type);
    :- Need(ty.Collection? && ty.finite, Invalid("`DisplayExpr` must be a finite collection."));
    var elems := ListUtils.ToSeq(de.Elements);
    var elems :- Seq.MapResult(elems, e requires e in elems reads * =>
      assume Decreases(e, de); TranslateExpression(e));
    Success(DE.Apply(DE.Eager(DE.Builtin(DE.Display(ty))), elems))
  }

  function method TranslateExpressionPair(mde: C.MapDisplayExpr, ep: C.ExpressionPair)
    : (e: TranslationResult<Expr>)
    reads *
    requires Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde)
    decreases ASTHeight(mde), 0
  {
    var tyA :- TranslateType(ep.A.Type);
    // TODO: This isn't really a sequence of type tyA! It should really construct pairs
    var ty := DT.Collection(true, DT.CollectionKind.Seq, tyA);
    var tA :- TranslateExpression(ep.A);
    var tB :- TranslateExpression(ep.B);
    Success(DE.Apply(DE.Eager(DE.Builtin(DE.Display(ty))), [tA, tB]))
  }

  function method TranslateMapDisplayExpr(mde: C.MapDisplayExpr)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(mde), 1
  {
    var ty :- TranslateType(mde.Type);
    :- Need(ty.Collection? && ty.kind.Map? && ty.finite, Invalid("`MapDisplayExpr` must be a map."));
    var elems := ListUtils.ToSeq(mde.Elements);
    var elems :- Seq.MapResult(elems, (ep: C.ExpressionPair) requires ep in elems reads * =>
      assume Math.Max(ASTHeight(ep.A), ASTHeight(ep.B)) < ASTHeight(mde);
      TranslateExpressionPair(mde, ep));
    Success(DE.Apply(DE.Eager(DE.Builtin(DE.Display(ty))), elems))
  }

  function method TranslateSeqSelectExpr(se: C.SeqSelectExpr): (e: TranslationResult<DE.T>)
    reads *
    decreases ASTHeight(se), 0
    ensures e.Success? ==> P.All_Expr(e.value, DE.WellFormed)
  { // FIXME: The models that we generate do not allow for `null`
    var ty :- TranslateType(se.Seq.Type);
    :- Need(ty.Collection? && !ty.kind.Set?,
            Invalid("`SeqSelect` must be on a map, sequence, or multiset."));
    :- Need(se.SelectOne ==> se.E0 != null && se.E1 == null,
            Invalid("Inconsistent values for `SelectOne` and E1 in SeqSelect."));
    :- Need(!se.SelectOne ==> ty.kind.Seq?,
            Invalid("`SeqSelect` on a map or multiset must have a single index."));
    assume Math.Max(ASTHeight(se.Seq), Math.Max(ASTHeight(se.E0), ASTHeight(se.E1))) < ASTHeight(se);
    var recv :- TranslateExpression(se.Seq);
    var eager := (op, args) => Success(DE.Apply(DE.Eager(op), args));
    match ty.kind { // FIXME AST gen should produce `Expression?` not `Expression`
      case Seq() =>
        if se.SelectOne then
          assert se.E1 == null;
          var e0 :- TranslateExpression(se.E0);
          eager(DE.BinaryOp(DE.BinaryOps.Sequences(DE.BinaryOps.SeqSelect)), [recv, e0])
        else if se.E1 == null then
          var e0 :- TranslateExpression(se.E0);
          eager(DE.BinaryOp(DE.BinaryOps.Sequences(DE.BinaryOps.SeqDrop)), [recv, e0])
        else if se.E0 == null then
          var e1 :- TranslateExpression(se.E1);
          eager(DE.BinaryOp(DE.BinaryOps.Sequences(DE.BinaryOps.SeqTake)), [recv, e1])
        else
          var e0 :- TranslateExpression(se.E0);
          var e1 :- TranslateExpression(se.E1);
          eager(DE.TernaryOp(DE.TernaryOps.Sequences(DE.TernaryOps.SeqSubseq)), [recv, e0, e1])
      case Map(_) =>
        assert se.SelectOne && se.E1 == null;
        var e0 :- TranslateExpression(se.E0);
        eager(DE.BinaryOp(DE.BinaryOps.Maps(DE.BinaryOps.MapSelect)), [recv, e0])
      case Multiset() =>
        assert se.SelectOne && se.E1 == null;
        var e0 :- TranslateExpression(se.E0);
        eager(DE.BinaryOp(DE.BinaryOps.Multisets(DE.BinaryOps.MultisetSelect)), [recv, e0])
    }
  }

  function method TranslateSeqUpdateExpr(se: C.SeqUpdateExpr)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(se), 0
  {
    var ty :- TranslateType(se.Type);
    :- Need(ty.Collection? && ty.kind != DT.Set(),
            Invalid("`SeqUpdate` must be a map, sequence, or multiset."));
    assume Math.Max(ASTHeight(se.Seq), Math.Max(ASTHeight(se.Index), ASTHeight(se.Value))) < ASTHeight(se);
    var tSeq :- TranslateExpression(se.Seq);
    var tIndex :- TranslateExpression(se.Index);
    var tValue :- TranslateExpression(se.Value);
    var op := match ty.kind
      case Seq() => DE.TernaryOps.Sequences(DE.TernaryOps.SeqUpdate)
      case Map(_) => DE.TernaryOps.Maps(DE.TernaryOps.MapUpdate)
      case Multiset() => DE.TernaryOps.Multisets(DE.TernaryOps.MultisetUpdate);
    Success(DE.Apply(DE.Eager(DE.TernaryOp(op)), [tSeq, tIndex, tValue]))
  }

  function method TranslateLambdaExpr(le: C.LambdaExpr)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(le), 0
  {
    var bvars := Seq.Map((bv: C.BoundVar) reads * => TypeConv.AsString(bv.Name),
      ListUtils.ToSeq(le.BoundVars));
    assume Decreases(le.Term, le);
    var body :- TranslateExpression(le.Term);
    Success(DE.Abs(bvars, body))
  }

  function method TranslateLetExpr(le: C.LetExpr)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(le), 0
  {
    :- Need(le.Exact, UnsupportedExpr(le));
    var lhss := ListUtils.ToSeq(le.LHSs);
    var bvs :- Seq.MapResult(lhss, (pat: C.CasePattern<C.BoundVar>) reads * =>
      :- Need(pat.Var != null, UnsupportedExpr(le));
      Success(TypeConv.AsString(pat.Var.Name)));
    var rhss := ListUtils.ToSeq(le.RHSs);
    var elems :- Seq.MapResult(rhss, e requires e in rhss reads * =>
      assume Decreases(e, le); TranslateExpression(e));
    :- Need(|bvs| == |elems|, UnsupportedExpr(le));
    assume Decreases(le.Body, le);
    var body :- TranslateExpression(le.Body);
    Success(DE.Bind(bvs, elems, body))
  }

  function method TranslateConcreteSyntaxExpression(ce: C.ConcreteSyntaxExpression)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(ce), 0
  {
    assume Decreases(ce.ResolvedExpression, ce);
    TranslateExpression(ce.ResolvedExpression)
  }

  function method TranslateITEExpr(ie: C.ITEExpr)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(ie), 0
  {
    // TODO: look at i.IsBindingGuard
    assume Decreases(ie.Test, ie);
    assume Decreases(ie.Thn, ie);
    assume Decreases(ie.Els, ie);
    var cond :- TranslateExpression(ie.Test);
    var thn :- TranslateExpression(ie.Thn);
    var els :- TranslateExpression(ie.Els);
    Success(DE.If(cond, thn, els))
  }

  function method TranslateExpression(c: C.Expression)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(c), 2
  {
    if c is C.IdentifierExpr then
      TranslateIdentifierExpr(c as C.IdentifierExpr)
    else if c is C.UnaryExpr then
      TranslateUnary(c as C.UnaryExpr)
    else if c is C.BinaryExpr then
      TranslateBinary(c as C.BinaryExpr)
    else if c is C.LiteralExpr then
      TranslateLiteral(c as C.LiteralExpr)
    else if c is C.ApplyExpr then
      TranslateApplyExpr(c as C.ApplyExpr)
    else if c is C.MemberSelectExpr then
      TranslateMemberSelectExpr(c as C.MemberSelectExpr)
    else if c is C.FunctionCallExpr then
      TranslateFunctionCallExpr(c as C.FunctionCallExpr)
    else if c is C.DatatypeValue then
      TranslateDatatypeValue(c as C.DatatypeValue)
    else if c is C.MapDisplayExpr then
      TranslateMapDisplayExpr(c as C.MapDisplayExpr)
    else if c is C.DisplayExpression then
      TranslateDisplayExpr(c as C.DisplayExpression)
    else if c is C.SeqUpdateExpr then
      TranslateSeqUpdateExpr(c as C.SeqUpdateExpr)
    else if c is C.SeqSelectExpr then
      TranslateSeqSelectExpr(c as C.SeqSelectExpr)
    else if c is C.LambdaExpr then
      TranslateLambdaExpr(c as C.LambdaExpr)
    else if c is C.LetExpr then
      TranslateLetExpr(c as C.LetExpr)
    else if c is C.ITEExpr then
      TranslateITEExpr(c as C.ITEExpr)
    else if c is C.ConcreteSyntaxExpression then
      TranslateConcreteSyntaxExpression(c as C.ConcreteSyntaxExpression)
    else Failure(UnsupportedExpr(c))
  }

  function method TranslatePrintStmt(p: C.PrintStmt)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(p), 0
  {
    var exprs :- Seq.MapResult(ListUtils.ToSeq(p.Args), TranslateExpression);
    Success(DE.Apply(DE.Eager(DE.Builtin(DE.Print)), exprs))
  }

  function method TranslateBlockStmt(b: C.BlockStmt)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(b), 0
  {
    var stmts := ListUtils.ToSeq(b.Body);
    var stmts' :- Seq.MapResult(stmts, s' requires s' in stmts reads * =>
      assume Decreases(s', b); TranslateStatement(s'));
    Success(DE.Block(stmts'))
  }

  function method TranslateIfStmt(i: C.IfStmt)
    : (e: TranslationResult<Expr>)
    reads *
    decreases ASTHeight(i), 0
  {
    // TODO: look at i.IsBindingGuard
    assume Decreases(i.Guard, i);
    assume Decreases(i.Thn, i);
    assume Decreases(i.Els, i);
    var cond :- TranslateExpression(i.Guard);
    var thn :- TranslateStatement(i.Thn);
    var els :- TranslateStatement(i.Els);
    Success(DE.If(cond, thn, els))
  }

  function method TranslateStatement(s: C.Statement)
    : TranslationResult<Expr>
    reads *
    decreases ASTHeight(s), 1
  {
    if s is C.PrintStmt then
      TranslatePrintStmt(s as C.PrintStmt)
    else if s is C.BlockStmt then
      TranslateBlockStmt(s as C.BlockStmt)
    else if s is C.IfStmt then
      TranslateIfStmt(s as C.IfStmt)
    else Failure(UnsupportedStmt(s))
  }

  function method TranslateMethod(m: C.Method)
    : TranslationResult<D.Method>
    reads *
  {
    // var compileName := m.CompileName;
    // FIXME “Main”
    var stmts :- Seq.MapResult(ListUtils.ToSeq(m.Body.Body), TranslateStatement);
    Success(D.Method("Main", DE.Block(stmts)))
  }

  function method TranslateProgram(p: C.Program)
    : TranslationResult<D.Program>
    reads *
  {
    var tm :- TranslateMethod(p.MainMethod);
    Success(D.Program(tm))
  }
}

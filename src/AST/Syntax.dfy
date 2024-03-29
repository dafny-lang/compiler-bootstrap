include "../Interop/CSharpDafnyModel.dfy"
include "../Utils/Library.dfy"
include "Locations.dfy"
include "Names.dfy"

module Bootstrap.AST.Syntax.Debug {
  import opened Locations

  datatype Unsupported =
    Unsupported(obj: string, prefix: string, loc: Location)
  {
    function method Message(): string {
      prefix + (if |prefix| > 0 then ": " else "") + obj
    }
  }
}

module Bootstrap.AST.Syntax {
  type Type = Types.T
  type BinaryOp = BinaryOps.T
  type TernaryOp = TernaryOps.T
  type UnaryOp = UnaryOps.T
  type Expr = Exprs.T
}

module Bootstrap.AST.Syntax.Types {
  import C = Microsoft.Dafny
  import opened Debug
  import opened Names

  datatype ClassType = ClassType(className: Name, typeArgs: seq<Type>)

  datatype CollectionKind =
    | Seq
    | Set
    | Multiset
    | Map(keyType: Type)

  datatype Type =
    | Unit
    | Bool
    | Char
    | Int
    | Real
    | BigOrdinal
    | BitVector(width: nat)
    | Collection(finite: bool, kind: CollectionKind, eltType: Type)
    | Function(args: seq<Type>, ret: Type) // TODO
    | Class(classType: ClassType)
    | Unsupported(un: Unsupported)
  {
    // TODO: remove?
    predicate method NoLeftFunction()
    {
      match this {
        case Unit => true
        case Bool => true
        case Char => true
        case Int => true
        case Real => true
        case BigOrdinal => true
        case BitVector(width: nat) => true
        case Collection(finite: bool, kind: CollectionKind, eltType: Type) =>
          && eltType.NoLeftFunction()
          && match kind {
            case Seq => true
            case Set => true
            case Multiset => true
            case Map(kt) => kt.NoLeftFunction()
          }
        case Function(args: seq<Type>, ret: Type) => false
        case Class(classType: ClassType) => false
        case Unsupported(_) => false
      }
    }

    // TODO: remove?
    predicate method WellFormed() {
      match this {
        case Unit => true
        case Bool => true
        case Char => true
        case Int => true
        case Real => true
        case BigOrdinal => true
        case BitVector(width: nat) => true
        case Collection(finite: bool, kind: CollectionKind, eltType: Type) =>
          && eltType.WellFormed()
          // This condition is overly restrictive: we will do the general case later.
          // For instance, maps can contain keys which don't have a decidable equality,
          // and sequences can contain elements which also don't have a decidable equality
          // (in which case we don't have a decidable equality over the sequences, but it
          // is fine).
          && eltType.NoLeftFunction()
          && match kind {
            case Seq => true
            case Set => eltType.NoLeftFunction()
            case Multiset => eltType.NoLeftFunction()
            case Map(kt) => kt.WellFormed() && kt.NoLeftFunction()
          }
        case Function(args: seq<Type>, ret: Type) =>
          && (forall i | 0 <= i < |args| :: args[i].WellFormed())
          && ret.WellFormed()
        case Class(classType: ClassType) =>
          && (forall i | 0 <= i < |classType.typeArgs| :: classType.typeArgs[i].WellFormed())
        case Unsupported(_) => true
      }
    }
  }

  type T(!new,00,==) = Type
}

module Bootstrap.AST.Syntax.BinaryOps {
  datatype Logical =
    Iff // And, Or, and Imp are in LazyOp
  datatype Eq =
    EqCommon | NeqCommon
  datatype Numeric =
    Lt | Le | Ge | Gt | Add | Sub | Mul | Div | Mod
  datatype BV =
    LeftShift | RightShift | BitwiseAnd | BitwiseOr | BitwiseXor
  datatype Char =
    LtChar | LeChar | GeChar | GtChar
  datatype Sequences =
    SeqEq | SeqNeq | Prefix | ProperPrefix | Concat | InSeq | NotInSeq |
    SeqSelect | SeqTake | SeqDrop // Separate nodes in DafnyAST.cs
  datatype Sets =
    SetEq | SetNeq | Subset | Superset | ProperSubset | ProperSuperset |
    Disjoint | InSet | NotInSet | Union | Intersection | SetDifference
  datatype Multisets =
    MultisetEq | MultisetNeq | MultiSubset | MultiSuperset |
    ProperMultiSubset | ProperMultiSuperset | MultisetDisjoint | InMultiset |
    NotInMultiset | MultisetUnion | MultisetIntersection | MultisetDifference |
    MultisetSelect // Separate node in DafnyAST.cs
  datatype Maps =
    MapEq | MapNeq | InMap | NotInMap | MapMerge | MapSubtraction |
    MapSelect // Separate node in DafnyAST.cs
  datatype Datatypes =
    RankLt | RankGt
  datatype BinaryOp =
    | Logical(oLogical: Logical)
    | Eq(oEq: Eq)
    | Numeric(oNumeric: Numeric)
    | BV(oBV: BV)
    | Char(oChar: Char)
    | Sequences(oSequences: Sequences)
    | Sets(oSets: Sets)
    | Multisets(oMultisets: Multisets)
    | Maps(oMaps: Maps)
    | Datatypes(oDatatypes: Datatypes)
  type T(!new,00,==) = BinaryOp
}

module Bootstrap.AST.Syntax.TernaryOps {
  import Types

  datatype Sequences =
    SeqUpdate | SeqSubseq
  datatype Multisets =
    MultisetUpdate
  datatype Maps =
    MapUpdate

  datatype TernaryOp =
    | Sequences(oSequences: Sequences)
    | Multisets(oMultisets: Multisets)
    | Maps(oMaps: Maps)

  type T(!new,00,==) = TernaryOp
}

module Bootstrap.AST.Syntax.UnaryOps {
  datatype UnaryOp =
    | BVNot
    | BoolNot
    | SeqLength
    | SetCard
    | MultisetCard
    | MapCard
    // Ghost operators
    // | Fresh
    // | Allocated
    // | Lit
  type T(!new,00,==) = UnaryOp
}

module Bootstrap.AST.Syntax.Exprs {
  import Utils.Lib.Math
  import Utils.Lib.Seq

  import Types
  import Names
  import UnaryOps
  import BinaryOps
  import TernaryOps
  import opened Debug
  import C = Microsoft.Dafny

  // FIXME should literals just be Values.T?
  datatype Literal =
    | LitUnit
    | LitThis
    | LitBool(b: bool)
    | LitInt(i: int)
    | LitReal(r: real)
    | LitChar(c: char)
    | LitString(s: string, verbatim: bool) // FIXME get rid of verbatim flag by unescaping
  {
    function method Depth() : nat { 1 }
  }

  datatype PredicateType =
    | Assert
    | Assume
    | Expect

  datatype BuiltinFunction =
    | Display(ty: Types.Type)
    | Predicate(predTy: PredicateType)
    | Print

  // DafnyAst.cs handles `f(1)` differently from `(var g := f; g)(1)`, but not us
  datatype EagerOp =
    | UnaryOp(uop: UnaryOps.T)
    | BinaryOp(bop: BinaryOps.T)
    | TernaryOp(top: TernaryOps.T)
    | Builtin(builtin: BuiltinFunction)
    | FunctionCall() // First argument is expression that resolves to function or method
    | MemberSelect(member: string)
    | DataConstructor(name: Names.Name, typeArgs: seq<Types.Type>)

  datatype LazyOp =
    | And
    | Or
    | Imp

  datatype ApplyOp =
    | Lazy(lOp: LazyOp)
    | Eager(eOp: EagerOp)

/// Notes on AST nodes
/// ==================
///
/// - AST nodes have type ``Expr``.  All subexpressions of a expression are
/// direct children of it; there are no subexpressions hidden within
/// ``ApplyOp``, for example).
///
/// - ``ApplyOp`` is split into lazy and eager operations.  This matter because
/// the language is not pure: if ``s`` is an empty sequence ``[]``, then the
/// expression ``false && s[0] == 1`` is a valid and reduces to ``false``,
/// whereas the expression ``0 * s[0] == 0`` is invalid and errors out with an
/// out-of-bounds access).
///
/// - ``Block`` is semantically the same as ``Bind`` with no variables.
///
/// - ``Bind`` is not the same as ``Apply`` on an ``Abs``, because variables are
/// captured by value, so mutations within an ``Abs`` are not propagated to the
/// caller's context. (In most cases, though, variables passed into an ``Abs``
/// are not mutated at all, because dafny lambdas are pure).

  datatype Expr =
    | Var(name: string)
    | Literal(lit: Literal)
    | Abs(vars: seq<string>, body: Expr)
    | Apply(aop: ApplyOp, args: seq<Expr>)
    | Block(stmts: seq<Expr>)
    | Bind(vars: seq<string>, vals: seq<Expr>, body: Expr)
    | If(cond: Expr, thn: Expr, els: Expr) // DISCUSS: Lazy op node?
    | Unsupported(un: Unsupported, children: seq<Expr>)
  {
    function method Depth() : nat {
      1 + match this {
        case Var(_) =>
          0
        case Literal(lit: Literal) =>
          0
        case Abs(vars, body) =>
          body.Depth()
        case Apply(_, args) =>
          Seq.MaxF(var f := (e: Expr) requires e in args => e.Depth(); f, args, 0)
        case Block(stmts) =>
          Seq.MaxF(var f := (e: Expr) requires e in stmts => e.Depth(); f, stmts, 0)
        case Bind(vars, vals, body) =>
          Math.Max(
            Seq.MaxF(var f := (e: Expr) requires e in vals => e.Depth(); f, vals, 0),
            body.Depth()
          )
        case If(cond, thn, els) =>
          Math.Max(cond.Depth(), Math.Max(thn.Depth(), els.Depth()))
        case Unsupported(_, args) =>
          Seq.MaxF(var f := (e: Expr) requires e in args => e.Depth(); f, args, 0)
      }
    }

    function method Children() : (s: seq<Expr>)
      ensures forall e' | e' in s :: e'.Depth() < this.Depth()
    {
      match this {
        case Var(_) => []
        case Literal(lit) => []
        case Abs(vars, body) => [body]
        case Apply(aop, exprs) => exprs
        case Block(exprs) => exprs
        case Bind(vars, vals, body) => vals + [body]
        case If(cond, thn, els) => [cond, thn, els]
        case Unsupported(_, children) => children
      }
    }
  }

  predicate method Supported(e: Expr) {
    !e.Unsupported?
  }

  predicate method WellFormed(e: Expr) {
    match e {
      case Apply(Lazy(_), es) =>
        |es| == 2
      case Apply(Eager(UnaryOp(_)), es) =>
        |es| == 1
      case Apply(Eager(BinaryOp(_)), es) =>
        |es| == 2
      case Apply(Eager(TernaryOp(top)), es) =>
        |es| == 3
      case Apply(Eager(FunctionCall()), es) =>
        |es| >= 1 // Needs a function to call
      case Apply(Eager(Builtin(Display(ty))), es) =>
        ty.Collection? && ty.finite
      case Bind(vars, vals, _) =>
        |vars| == |vals|
      case _ => true
    }
  }

  function method ConstructorsMatch(e: Expr, e': Expr): bool {
    match e {
      case Var(name) =>
        e'.Var? && name == e'.name
      case Literal(l) =>
        e'.Literal? && l == e'.lit
      case Abs(vars, body) =>
        e'.Abs? && vars == e'.vars
      case Apply(aop, args) =>
        e'.Apply? && aop == e'.aop && |args| == |e'.args|
      case Block(stmts) =>
        e'.Block? && |stmts| == |e'.stmts|
      case If(cond, thn, els) =>
        e'.If?
      case Bind(vars, vals, body) =>
        e'.Bind? && |vars| == |e'.vars| && |vals| == |e'.vals|
      case Unsupported(un, children) =>
        e'.Unsupported? &&
        e'.un == un &&
        |e'.children| == |children|
    }
  }

  type T(!new,00,==) = Expr
}

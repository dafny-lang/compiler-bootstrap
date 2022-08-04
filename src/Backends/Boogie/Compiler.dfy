include "../../Interop/CSharpDafnyASTModel.dfy"
include "../../Interop/CSharpInterop.dfy"
include "../../Interop/CSharpDafnyInterop.dfy"
include "../../AST/Translator.dfy"
include "../../Passes/EliminateNegatedBinops.dfy"
include "../../Transforms/BottomUp.dfy"
include "../../Utils/Library.dfy"
include "../../Utils/StrTree.dfy"
include "../../../../../../BoogieV/lang/BoogieLang.dfy"

module {:options "-functionSyntax:4"}
  Bootstrap.Backends.Boogie.Compiler
{
  import AST.Predicates
  import BLib = Wrappers
  import BV = BoogieLang
  import Passes.EliminateNegatedBinops
  import Transforms.BottomUp
  import Transforms.Generic
  import Utils.StrTree
  import opened AST.Predicates.Deep
  import opened AST.Syntax
  import opened Interop.CSharpDafnyInterop
  import opened Utils.Lib.Datatypes

  type WfExpr = e: Exprs.T | Deep.All_Expr(e, Exprs.WellFormed) witness *

  function TranslateLiteralExpr(l: Exprs.Literal) : BV.Expr
    requires l.LitInt? || l.LitBool?
  {
    match l {
      case LitBool(b) => BV.ELit(BV.LitBool(b))
      case LitInt(i) => BV.ELit(BV.LitInt(i))
    }
  }

  function TranslateLazyExpr(op: Exprs.LazyOp, e0: BV.Expr, e1: BV.Expr) : BV.Expr {
    var bop := match op
      case And => BV.Binop.And
      case Or => BV.Binop.Or
      case Imp => BV.Binop.Imp;
    BV.BinOp(e0, bop, e1)
  }

  function TranslateUnaryOpExpr(op: UnaryOp, e: BV.Expr) : BV.Expr {
    var uop := match op
      case BoolNot() => BV.Not
      case BVNot() => Crash("BVNot")
      case SeqLength() => Crash("SeqLength")
      case SetCard() => Crash("SetCard")
      case MultisetCard() => Crash("MultisetCard")
      case MapCard() => Crash("MapCard")
      case MemberSelect(_) => Crash("MemberSelect");
    BV.UnOp(uop, e)
  }

  function TranslateBinaryExpr(op: BinaryOp, e0: BV.Expr, e1: BV.Expr) : BV.Expr {
    var bop := match op
      case Logical(Iff) => BV.Iff

      case Eq(EqCommon) => BV.Eq
      case Eq(NeqCommon) => BV.Neq

      case Numeric(Lt) => BV.Lt
      case Numeric(Le) => BV.Le
      case Numeric(Ge) => BV.Ge
      case Numeric(Gt) => BV.Gt
      case Numeric(Add) => BV.Add
      case Numeric(Sub) => BV.Sub
      case Numeric(Mul) => BV.Mul
      case Numeric(Div) => BV.Div
      case Numeric(Mod) => BV.Mod

      case _ => Crash("BinOp");
    BV.BinOp(e0, bop, e1)
  }

  function Crash<A>(msg: string): (a: A) {
    assume false;
    Crash(msg)
  } by method {
    print msg;
    expect false;
    a := Crash(msg);
  }

  function Annotated<A, T>(a: A, annot: T): A {
    a
  }

  predicate SupportsVerification_Expr(e: Expr) {
    Exprs.WellFormed(e) &&
    match e {
      case Var(x) => true
      case Literal(l) =>
        l.LitInt? || l.LitBool?
      case Abs(_, _) =>
        Annotated(false, "Expr.Abs")
      case Apply(op, es) =>
        && (forall e <- es :: SupportsVerification_Expr(e))
        && match op {
            case Lazy(op) => true
            case Eager(UnaryOp(op)) => true
            case Eager(BinaryOp(op)) => true
            case Eager(TernaryOp(op)) => Annotated(false, "Expr.TernaryOp")
            case Eager(Builtin(Display(ty))) => Annotated(false, "Expr.Builtin(Display)")
            case Eager(Builtin(Progn)) => Annotated(false, "Expr.Builtin(Progn)")
            case Eager(Builtin(Assert)) => Annotated(false, "Expr.Builtin(Assert)")
            case Eager(Builtin(Print)) => Annotated(false, "Expr.Builtin(Print)")
            case Eager(DataConstructor(name, typeArgs)) => Annotated(false, "Expr.DataConstructor")
            case Eager(FunctionCall()) => Annotated(false, "Expr.FunctionCall")
          }
      case Block(exprs) =>
        Annotated(false, "Expr.Block")
      case Bind(vars, vals, body) =>
        && |vars| == |vals| == 1
        && (forall e <- vals :: SupportsVerification_Expr(e))
        && SupportsVerification_Expr(body)
      case If(cond, thn, els) =>
        Annotated(false, "Expr.If")
    }
  }

  predicate SupportsVerification_Stmt(s: Expr) {
    match s {
      case Var(_) => Annotated(false, "Stmt.Var")
      case Literal(l) => Annotated(false, "Stmt.Literal")
      case Abs(_, _) => Annotated(false, "Stmt.Abs")
      case Apply(op, es) =>
        match op {
          case Eager(Builtin(Assert)) => (forall e <- es :: SupportsVerification_Expr(e))
          case Eager(Builtin(Progn)) => (forall e <- es :: SupportsVerification_Stmt(e))
          case _ => Annotated(false, "Stmt.Apply")
        }
      case Block(exprs) =>
        && (forall e <- exprs :: SupportsVerification_Stmt(e))
      case Bind(vars, vals, body) =>
        && |vars| == |vals| == 1
        && (forall e <- vals :: SupportsVerification_Expr(e))
        && SupportsVerification_Stmt(body)
      case If(cond, thn, els) =>
        && SupportsVerification_Expr(cond)
        && SupportsVerification_Stmt(thn)
        && SupportsVerification_Stmt(els)
    }
  }

  // FIXME(CPC): Predicate to characterize supported terms?

  function TranslateExpr(e: WfExpr) : BV.Expr
    requires SupportsVerification_Expr(e)
    decreases e, 0
  {
    match e {
      case Var(x) =>
        BV.Var(x)
      case Literal(l) =>
        TranslateLiteralExpr(l)
      case Apply(op, es) =>
        match op {
          case Lazy(op) =>
            var c0, c1 := TranslateExpr(es[0]), TranslateExpr(es[1]);
            TranslateLazyExpr(op, c0, c1)
          case Eager(UnaryOp(op)) =>
            TranslateUnaryOpExpr(op, TranslateExpr(es[0]))
          case Eager(BinaryOp(op)) =>
            TranslateBinaryExpr(op, TranslateExpr(es[0]), TranslateExpr(es[1]))
        }
      case Bind(vars, vals, body) =>
        assert |vars| == |vals| == 1;
        var decls := Seq.Map(x requires x in vars => (x, BV.Ty.TPrim(BV.PrimTy.TInt)), vars);
        BV.Let(vars[0], TranslateExpr(vals[0]), TranslateExpr(body))
    }
  }

  function TranslateStmt(e: WfExpr) : BV.Cmd
    requires SupportsVerification_Stmt(e)
    decreases e, 0
  {
    match e {
      case Apply(op, args) =>
        match op {
          case Eager(Builtin(Assert)) =>
            BV.SimpleCmd(BV.Assert(TranslateExpr(args[0])))
          case Eager(Builtin(Progn)) =>
            var bexprs := Seq.Map(x requires x in args => TranslateStmt(x), args);
            Seq.FoldR((acc, x) => BV.Seq(x, acc), BV.SimpleCmd(BV.Skip), bexprs)
        }
      case Block(exprs) =>
        var bexprs := Seq.Map(x requires x in exprs => TranslateStmt(x), exprs);
        Seq.FoldR((acc, x) => BV.Seq(x, acc), BV.SimpleCmd(BV.Skip), bexprs)
      case Bind(vars, vals, body) =>
        // TODO: Assumes all variables are int
        var decls := Seq.Map(x requires x in vars => (x, BV.Ty.TPrim(BV.PrimTy.TInt)), vars);
        BV.Scope(labelName := BLib.None, varDecls := decls, body := TranslateStmt(body))
      case If(cond, thn, els) =>
        BV.If(BLib.Some(TranslateExpr(cond)), TranslateStmt(thn), TranslateStmt(els))
    }
  }

  function WellFormednessAssertion1(e: WfExpr): Option<WfExpr>
  {
    Predicates.Deep.AllImpliesChildren(e, Exprs.WellFormed);
    match e {
      case Var(_) => None
      case Literal(l) => None
      case Abs(_, _) => None
      case Apply(Lazy(op), es) => None
      case Apply(Eager(op), es) =>
        match op {
          case BinaryOp(Numeric(Div)) => Some(Neq(es[1], Zero))
          case _ => None
        }
      case Block(es) => None
      case Bind(vars, es, body) => None
      case If(cond, thn, els) => None
    }
  }

  function AddAssertion(assertion: WfExpr, e: WfExpr): (e': WfExpr) {
    Progn([Assert(assertion), e])
  }

  function AddWellFormednessAssertions1(e: WfExpr): (e': WfExpr) {
    match WellFormednessAssertion1(e)
      case Some(wf) => AddAssertion(wf, e)
      case None => e
  }

  const AddWellFormednessAssertionsTR: BottomUp.BottomUpTransformer :=
    assume false; Generic.TR(AddWellFormednessAssertions1, _ => true);

  // FIXME move / remove?
  function ReplaceChildren(e: Expr, children: seq<Expr>): (e': Expr)
    requires |children| == |e.Children()|
  {
    match e {
      case Var(_) => e
      case Literal(lit) => e
      case Abs(vars, body) => Exprs.Abs(vars, children[0])
      case Apply(aop, exprs) => Exprs.Apply(aop, children)
      case Block(exprs) => Exprs.Block(children)
      case Bind(vars, vals, body) =>
        Exprs.Bind(vars, children[..|children| - 1], children[|children| - 1])
      case If(cond, thn, els) =>
        Exprs.If(children[0], children[1], children[2])
    }
  }

  function RemoveProgns1(e: Expr): (e': Expr)
  {
    if e.Apply? && e.aop == OpProgn && |e.args| == 1 then e.args[0]
    else e
  }

  const RemovePrognTR: BottomUp.BottomUpTransformer :=
    assume false; Generic.TR(RemoveProgns1, _ => true)

  const True: WfExpr :=
    Exprs.Literal(Exprs.LitBool(true))
  const Zero: WfExpr :=
    Exprs.Literal(Exprs.LitInt(0))
  const And: (WfExpr, WfExpr) -> WfExpr :=
    (a, b) => Exprs.Apply(Exprs.Lazy(Exprs.And), [a, b])
  const Imp: (WfExpr, WfExpr) -> WfExpr :=
    (a, b) => Exprs.Apply(Exprs.Lazy(Exprs.Imp), [a, b])
  const Not: (WfExpr) -> WfExpr :=
    (a) => Exprs.Apply(Exprs.Eager(Exprs.UnaryOp(UnaryOps.BoolNot)), [a])
  const Neq: (WfExpr, WfExpr) -> WfExpr :=
    (a, b) => Exprs.Apply(Exprs.Eager(Exprs.BinaryOp(BinaryOps.Eq(BinaryOps.NeqCommon))), [a, b])
  const OpAssert :=
    Exprs.Eager(Exprs.Builtin(Exprs.Assert))
  const Assert: (WfExpr) -> WfExpr :=
    (e) => Exprs.Apply(OpAssert, [e])
  const OpProgn :=
    Exprs.Eager(Exprs.Builtin(Exprs.Progn))
  const Progn: (seq<WfExpr>) --> WfExpr :=
    (es) requires |es| > 0 => var wf: WfExpr := Exprs.Apply(OpProgn, es); wf

  function RemoveNone<A>(opts: seq<Option<A>>): seq<A> {
    if |opts| == 0 then []
    else if opts[0].Some? then [opts[0].value] + RemoveNone(opts[1..])
    else RemoveNone(opts[1..])
  }

  function Unzip<A, B>(zipped: seq<(A, B)>): (p: (seq<A>, seq<B>))
    ensures |p.0| == |p.1| == |zipped|
  {
    if |zipped| == 0 then ([], [])
    else
      var (sA, sB) := Unzip(zipped[1..]);
      (([zipped[0].0] + sA), ([zipped[0].1] + sB))
  }

  function PeelOffAssert(e: WfExpr): (e': (Option<WfExpr>, WfExpr)) {
    Predicates.Deep.AllImpliesChildren(e, Exprs.WellFormed);
    if e.Apply? && e.aop == OpProgn && |e.args| > 1 then
      var fst: Expr := e.args[0];
      Predicates.Deep.AllImpliesChildren(fst, Exprs.WellFormed);
      if fst.Apply? && fst.aop == OpAssert then
          assert |fst.args| == 1;
          (Some(fst.args[0]), Progn(e.args[1..]))
      else (None, e)
    else (None, e)
  }

  function PeelOffAsserts(es: seq<WfExpr>): (pairs: (seq<Option<WfExpr>>, seq<WfExpr>))
    ensures |pairs.0| == |pairs.1| == |es|
  {
    Unzip(Seq.Map(e requires e in es => PeelOffAssert(e), es))
  }

  function MergeAsserts(wfs: seq<WfExpr>): (wf: WfExpr) {
    if |wfs| == 0 then True
    else if |wfs| == 1 then wfs[0]
    else And(wfs[0], MergeAsserts(wfs[1..]))
  }

  function AddAssertions(wfs: seq<WfExpr>, e: WfExpr): (e': WfExpr) {
    if |wfs| == 0 then e
    else AddAssertion(MergeAsserts(wfs), e)
  }

  function LiftAsserts1(e: WfExpr): (e': WfExpr) {
    match e {
      case Var(_) => e
      case Literal(lit) => e
      case Abs(vars, body) =>
        Crash<WfExpr>("LiftAssert.Abs")
      case Apply(op, exprs) =>
        var (wfs, exprs) := PeelOffAsserts(exprs);
        var wfs := match op {
          case Lazy(And) | Lazy(Imp) =>
            [wfs[0], wfs[1].Map(wf => Imp(exprs[0], wf))]
          case Lazy(Or) =>
            [wfs[0], wfs[1].Map(wf => Imp(Not(exprs[0]), wf))]
          case _ => wfs
        };
        AddAssertions(RemoveNone(wfs), Exprs.Apply(op, exprs))
      case Block(exprs) =>
        var (wfs, exprs) := PeelOffAsserts(exprs);
        AddAssertions(RemoveNone(wfs), Exprs.Block(exprs))
      case Bind(vars, vals, body) =>
        var (wfs_vals, vals) := PeelOffAsserts(vals);
        var (wf_body, body) := PeelOffAssert(body);
        var wf_body: Option<WfExpr> := wf_body.Map(wf => Exprs.Bind(vars, vals, wf));
        AddAssertions(RemoveNone(wfs_vals + [wf_body]), Exprs.Bind(vars, vals, body))
      case If(cond, thn, els) =>
        var (wf_cond, cond) := PeelOffAssert(cond);
        var (wf_thn, thn) := PeelOffAssert(thn);
        var (wf_els, els) := PeelOffAssert(els);
        var wf_thn := wf_thn.Map(wf => Imp(cond, wf));
        var wf_els := wf_els.Map(wf => Imp(Not(cond), wf));
        AddAssertions(RemoveNone([wf_cond, wf_thn, wf_els]), Exprs.If(cond, thn, els))
    }
  }

  const LiftAssertsTR: BottomUp.BottomUpTransformer :=
    assume false; Generic.TR(LiftAsserts1, _ => true)

  function TranslateMethod(m: Method) : BV.Cmd
    requires Deep.All_Method(m, Exprs.WellFormed)
    requires Shallow.All_Method(m, SupportsVerification_Stmt)
  {
    match m {
      case Method(nm, methodBody) => TranslateStmt(methodBody)
    }
  }

  function TranslateProgram(p: Program) : BV.Cmd
    requires Deep.All_Program(p, Exprs.WellFormed)
    requires Shallow.All_Program(p, SupportsVerification_Stmt)
  {
    match p {
      case Program(mainMethod) => TranslateMethod(mainMethod)
    }
  }

  function CompileProgram(p: Program) : Result<BV.Cmd, string>
  {
    :- Need(Deep.All_Program(p, Exprs.WellFormed), "Well-formedness check failed.");

    var p :=
      assume false;
      var p := BottomUp.Map_Program(p, AddWellFormednessAssertionsTR);
      var p := BottomUp.Map_Program(p, LiftAssertsTR);
      var p := BottomUp.Map_Program(p, RemovePrognTR);
      p;

    :- Need(Shallow.All_Program(p, SupportsVerification_Stmt), "Structure check failed");

    Success(TranslateProgram(p))
  }

  function Compile(p: Program) : StrTree.StrTree {
    StrTree.Str(
      match CompileProgram(p)
        case Success(vc) => vc.ToString(indent := 0)
        case Failure(msg) => "!! " + msg
    )
  }
}

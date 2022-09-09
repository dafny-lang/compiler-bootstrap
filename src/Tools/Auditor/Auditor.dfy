include "../../AST/Entities.dfy"
include "../../AST/Names.dfy"
include "../../AST/Syntax.dfy"
include "../../AST/Translator.Entity.dfy"
include "../../Interop/CSharpDafnyASTModel.dfy"
include "../../Interop/CSharpDafnyInterop.dfy"
include "../../Utils/Library.dfy"
include "Report.dfy"

module {:extern "Bootstrap.Tools.Auditor"} {:options "-functionSyntax:4"} Bootstrap.Tools.Auditor {

  import opened AST.Entities
  import opened AST.Names
  import opened AST.Predicates
  import opened AST.Syntax.Exprs
  import E = AST.Translator.Entity
  import opened AuditReport
  import opened Interop
  import opened Utils.Lib.Datatypes
  import opened Utils.Lib.Seq

  //// AST traversals ////

  predicate IsAssumeStatement(e: Expr)
  {
    && e.Apply?
    && e.aop.Eager?
    && e.aop.eOp.Builtin?
    && e.aop.eOp.builtin.Predicate?
    && e.aop.eOp.builtin.predTy.Assume?
  }

  predicate ContainsAssumeStatement(e: Expr)
    decreases e.Depth()
  {
    Deep.Any_Expr(e, (c:Expr) => IsAssumeStatement(c))
  }

  //// Tag extraction and processing ////

  function TagIf(cond: bool, t: Tag): set<Tag> {
    if cond then {t} else {}
  }

  function GetTags(e: Entity): set<Tag> {
    TagIf(exists a | a in e.ei.attrs :: a.name == Extern, HasExternAttribute) +
    TagIf(exists a | a in e.ei.attrs :: a.name == Axiom, HasAxiomAttribute) +
    TagIf(e.Type? && e.t.SubsetType?, IsSubsetType) +
    TagIf(e.Type? && e.t.NewType? && e.t.nt.pred.Some?, IsSubsetType) +
    TagIf(e.Type? && e.t.SubsetType? && e.t.st.witnessExpr.None?, HasNoWitness) +
    TagIf(e.Type? && e.t.NewType? && e.t.nt.witnessExpr.None?, HasNoWitness) +
    TagIf(e.Definition? && e.d.Callable? && e.d.ci.body.None?, HasNoBody) +
    TagIf(e.Definition? && e.d.Callable? && e.d.ci.body.Some? &&
          ContainsAssumeStatement(e.d.ci.body.value), HasAssumeInBody) +
    TagIf(e.Definition? && e.d.Callable? && |e.d.ci.ens| > 0, HasEnsuresClause) +
    TagIf(e.Definition? && e.d.Callable? && |e.d.ci.req| > 0, HasRequiresClause) +
    TagIf(e.Definition? && e.d.Callable?, IsCallable)
  }

  //// Report generation ////

  function AddAssumptions(e: Entity, rpt: Report): Report {
    var tags := GetTags(e);
    if IsAssumption(tags)
      then Report(rpt.assumptions + [Assumption(e.ei.name.ToString(), tags)])
      else rpt
  }

  function FoldEntities<T(!new)>(f: (Entity, T) -> T, reg: Registry_, init: T): T {
    var names := reg.SortedNames();
    FoldL((a, n) requires reg.Contains(n) => f(reg.Get(n), a), init, names)
  }

  function GenerateAuditReport(reg: Registry_): Report {
    FoldEntities(AddAssumptions, reg, EmptyReport)
  }

  class {:extern} DafnyAuditor {
    constructor() {
    }

    method Audit(p: CSharpDafnyASTModel.Program) returns (r: string)
    {
      var res := E.TranslateProgram(p);
      match res {
        case Success(p') =>
          var rpt := GenerateAuditReport(p'.registry);
          return RenderAuditReportMarkdown(rpt);
        case Failure(err) =>
          return err.ToString();
      }
    }
  }
}

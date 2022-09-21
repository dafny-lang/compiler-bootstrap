include "../../AST/Entities.dfy"
include "../../AST/Names.dfy"
include "../../AST/Syntax.dfy"
include "../../AST/Translator.Entity.dfy"
include "../../Interop/CSharpDafnyASTModel.dfy"
include "../../Interop/CSharpDafnyInterop.dfy"
include "../../Interop/CSharpModel.dfy"
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
  import opened Interop.CSharpDafnyInterop
  import opened Interop.CSharpInterop
  import opened Utils.Lib.Datatypes
  import opened Utils.Lib.Seq
  import System

/// ## AST traversals

  predicate IsAssumeStatement(e: Expr)
  {
    && e.Apply?
    && e.aop == Eager(Builtin(Predicate(Assume)))
  }

  predicate ContainsAssumeStatement(e: Expr)
    decreases e.Depth()
  {
    Deep.Any_Expr(e, (c:Expr) => IsAssumeStatement(c))
  }

/// ## Tag extraction and processing

  function TagIf(cond: bool, t: Tag): set<Tag> {
    if cond then {t} else {}
  }

  function GetTags(e: Entity): set<Tag> {
    // TODO: support MayNotTerminate
    TagIf(exists a <- e.ei.attrs :: a.name == Extern, HasExternAttribute) +
    TagIf(exists a <- e.ei.attrs :: a.name == Axiom, HasAxiomAttribute) +
    TagIf(e.Type? && e.t.SubsetType?, IsSubsetType) +
    TagIf(e.Type? && e.t.SubsetType? && e.t.st.witnessExpr.None?, MissingWitness) +
    TagIf(e.Definition? && e.d.Callable? && e.d.ci.body.None?, MissingBody) +
    TagIf(e.Definition? && e.d.Callable? && e.d.ci.body.Some? &&
          exists exp <- e.Exprs() :: ContainsAssumeStatement(exp), HasAssumeInBody) +
    TagIf(e.Definition? && e.d.Callable? && |e.d.ci.ens| > 0, HasEnsuresClause) +
    TagIf(e.Definition? && e.d.Callable? && |e.d.ci.req| > 0, HasRequiresClause) +
    TagIf(e.Definition? && e.d.Callable?, IsCallable)
  }

/// ## Report generation

  function AddAssumptions(e: Entity, assms: seq<Assumption>): seq<Assumption> {
    var tags := GetTags(e);
    if IsAssumption(tags) then
      assms + [Assumption(e.ei.name.ToDafnyName(), e.ei.location, tags)]
    else
      assms
  }

  function FoldEntities<T(!new)>(f: (Entity, T) -> T, reg: Registry_, init: T): T {
    var names := Seq.Filter(reg.SortedNames(), (n: Name) => !n.IsInternal());
    FoldL((a, n) requires reg.Contains(n) => f(reg.Get(n), a), init, names)
  }

  function GenerateAuditReport(reg: Registry_): Report {
    Report(FoldEntities(AddAssumptions, reg, []))
  }

  class {:extern} DafnyAuditor {

    constructor() {
    }

    method Audit(render: Report -> string, p: CSharpDafnyASTModel.Program) returns (r: string)
    {
      var res := E.TranslateProgram(p, includeCompileModules := false);
      match res {
        case Success(p') =>
          var rpt := GenerateAuditReport(p'.registry);
          return render(rpt);
        case Failure(err) =>
          return "Failed to translate program:\n" + err.ToString();
      }
    }

    method AuditHTML(p: CSharpDafnyASTModel.Program) returns (r: string)
    {
      r := Audit(RenderAuditReportHTML, p);
    }

    method AuditMarkdown(p: CSharpDafnyASTModel.Program) returns (r: string)
    {
      r := Audit(RenderAuditReportMarkdown, p);
    }

    method AuditText(p: CSharpDafnyASTModel.Program) returns (r: string)
    {
      r := Audit(RenderAuditReportText, p);
    }

    method WarnReport(reporter: Microsoft.Dafny.ErrorReporter, rpt: Report) {
      for i := 0 to |rpt.assumptions| {
        var a := rpt.assumptions[i];
        var descs := AssumptionDescription(a.tags);
        for j := 0 to |descs| {
          var desc := descs[j];
          var msg := AssumptionWarning(a, desc);
          adapter.Message(Dafny.MessageSource.Rewriter, Dafny.ErrorLevel.Warning, a.location, msg);
        }
      }
    }

    method AuditWarnings(reporter: Microsoft.Dafny.ErrorReporter, p: CSharpDafnyASTModel.Program)
    {
      var res := E.TranslateProgram(p, includeCompileModules := false);
      var adapter := new Locations.ReporterAdapter(reporter);
      match res {
        case Success(p') =>
          var rpt := GenerateAuditReport(p'.registry);
          WarnReport(reporter, rpt);
        case Failure(err) =>
          var tok := p.DefaultModuleDef.tok;
          var msg := StringUtils.ToCString("Failed to translate program. " + err.ToString());
          reporter.Message(Dafny.MessageSource.Rewriter, Dafny.ErrorLevel.Error, tok, msg);
      }
    }
  }
}

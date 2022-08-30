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
  import opened AST.Syntax.Exprs
  import E = AST.Translator.Entity
  import opened AuditReport
  import opened Interop
  import opened Utils.Lib.Datatypes
  import opened Utils.Lib.Seq

  //// AST traversals ////

  // TODO: can't be implemented yet because there's no representation for `assume`
  //predicate ContainsAssumeStatement(e: Expr)

  //// Tag extraction and processing ////

  function TagIf(cond: bool, t: Tag): set<Tag> {
    if cond then {t} else {}
  }

  function GetTags(e: Entity): set<Tag> {
    TagIf(exists a | a in e.ei.attrs :: a.name == Extern, HasExternAttribute) +
    TagIf(exists a | a in e.ei.attrs :: a.name == Axiom, HasAxiomAttribute) +
    TagIf(e.Type? && e.t.SubsetType? && e.t.st.witnessExpr.None?, HasNoWitness) +
    TagIf(e.Definition? && e.d.Callable? && e.d.ci.body.None?, HasNoBody) +
    //TagIf(e.Definition? && e.d.Callable? && ContainsAssumeStatement(e.d.ci.body), HasAssumeInBody) +
    TagIf(e.Definition? && e.d.Callable? && |e.d.ci.ens| > 0, HasEnsuresClause)
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

    function Audit(p: CSharpDafnyASTModel.Program): string
      reads *
    {
      var res := E.TranslateProgram(p);
      match res {
        case Success(reg) =>
          var rpt := GenerateAuditReport(reg);
          RenderAuditReportMarkdown(rpt)
        case Failure(err) => err.ToString()
      }
    }
  }
}
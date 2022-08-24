include "../../AST/Entities.dfy"
include "../../AST/Names.dfy"
include "../../AST/Syntax.dfy"
include "../../AST/Translator.Entities.dfy"
include "../../Interop/CSharpDafnyASTModel.dfy"
include "../../Interop/CSharpDafnyInterop.dfy"
include "../../Utils/Library.dfy"
include "Report.dfy"

import opened Bootstrap.AST.Entities
import opened Bootstrap.AST.Names
import opened Bootstrap.AST.Syntax.Exprs
import opened Bootstrap.AST.EntityTranslator
import opened AuditReport
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
  TagIf(e.Definition? && e.d.Callable? /*&& e.d.ci.body.None?*/, HasNoBody) +
  //TagIf(e.Definition? && e.d.Callable? && ContainsAssumeStatement(e.d.ci.body), HasNoBody) +
  TagIf(e.Definition? && e.d.Callable? /*&& e.d.ci.ensures.Some?*/, HasEnsuresClause)
}

//// Rport generation ////

function AddAssumptions(e: Entity, rpt: Report): Report {
  var tags := GetTags(e);
  if IsAssumption(tags)
    then Report(rpt.assumptions + [Assumption(e.ei.name.ToString(), tags)])
    else rpt
}

function FoldEntities<T(!new)>(f: (Entity, T) -> T, reg: Registry, init: T): T {
  var names := reg.SortedNames();
  FoldL((a, n) requires reg.Contains(n) => f(reg.Get(n), a), init, names)
}

function GenerateAuditReport(reg: Registry): Report {
  FoldEntities(AddAssumptions, reg, EmptyReport)
}

function {:export} Audit(p: Bootstrap.Interop.CSharpDafnyASTModel.Program): string
  reads *
{
  var res := TranslateProgram(p);
  match res {
    case Success(p') =>
      var rpt := GenerateAuditReport(p'.registry);
      RenderAuditReportMarkdown(rpt)
    case Failure(err) => err.ToString()
  }
}

//// Later functionality ////

/*
predicate EntityDependsOn(client: Entity, target: Entity)

function ImmediateDependents(e: Entity): set<Entity>

function TransitiveDependents(e: Entity): set<Entity>
*/

include "../../AST/Entities.dfy"
include "../../Utils/Library.dfy"

module Bootstrap.Tools.AuditReport {
  import opened AST.Entities
  import opened Utils.Lib.Seq

  /// ## Data types for report

  datatype Tag =
    | IsGhost
    | IsSubsetType
    | IsCallable
    | MissingBody
    | HasAxiomAttribute
    | HasExternAttribute
    | HasVerifyFalseAttribute
    | HasAssumeInBody // Maybe: (expr: Expression) TODO: :axiom?
    | HasRequiresClause
    | HasEnsuresClause
    | MissingWitness
    | HasJustification
    | MayNotTerminate
    {
      function method ToString(): string {
        match this {
          case IsGhost => "IsGhost"
          case IsSubsetType => "IsSubsetType"
          case IsCallable => "IsCallable"
          case MissingBody => "MissingBody"
          case HasAxiomAttribute => "HasAxiomAttribute"
          case HasExternAttribute => "HasExternAttribute"
          case HasVerifyFalseAttribute => "HasVerifyFalseAttribute"
          case HasAssumeInBody => "HasAssumeInBody"
          case HasRequiresClause => "HasRequiresClause"
          case HasEnsuresClause => "HasEnsuresClause"
          case MissingWitness => "MissingWitness"
          case HasJustification => "HasJustification"
          case MayNotTerminate => "MayNotTerminate"
        }
      }
    }

  datatype Assumption =
    Assumption(name: string, location: Location, tags: set<Tag>)

  datatype Report =
    Report(assumptions: seq<Assumption>)

  const EmptyReport := Report([])

  /// ## Tag categorization

  predicate method IsAssumption(ts: set<Tag>) {
    // This seems to be of little value at the moment
    // || (IsSubsetType in ts && MissingWitness in ts)
    || HasAxiomAttribute in ts
    || (&& IsCallable in ts
        && (|| (HasEnsuresClause in ts && (MissingBody in ts || HasExternAttribute in ts))
            || HasAssumeInBody in ts))
    || MayNotTerminate in ts
    // TODO: extern with no ensures but possibly empty type
    // TODO: loop or forall with no body
  }

  predicate method IsExplicitAssumption(ts: set<Tag>) {
    || HasAxiomAttribute in ts
    || HasAssumeInBody in ts
  }

  /// ## Report rendering

  function method BoolYN(b: bool): string {
    if b then "Y" else "N"
  }

  function method MaybeElt<T>(b: bool, elt: T): seq<T> {
     if b then [elt] else []
  }

  function method AssumptionDescription(ts: set<Tag>): seq<(string, string)> {
    MaybeElt(IsCallable in ts && MissingBody in ts && IsGhost in ts,
      ("Ghost declaration has no body.",
       "Provide a body or add `{:axiom}`.")) +
    MaybeElt(IsCallable in ts && MissingBody in ts && !(IsGhost in ts),
      ("Compiled declaration has no body.",
       "Provide a body or add `{:axiom}`.")) +
    MaybeElt(HasExternAttribute in ts && HasRequiresClause in ts,
      ("Declaration with `{:extern}` has precondition.",
       "Extensively test client code.")) +
    MaybeElt(HasExternAttribute in ts && HasEnsuresClause in ts,
      ("Declaration with `{:extern}` has postcondition.",
       "Extensively test against external code.")) +
       /*
    MaybeElt(IsSubsetType in ts && MissingWitness in ts,
      ("Subset type has no witness and could be empty.",
       "Provide a witness.")) +
       */
    MaybeElt(HasAxiomAttribute in ts,
      ("Declaration has explicit `{:axiom}` attribute.",
       "Attempt to provide a proof or test.")) +
    MaybeElt(MayNotTerminate in ts,
      ("Method may not terminate (uses `decreases *`).",
       "Provide a valid `decreases` clause.")) +
    MaybeElt(HasAssumeInBody in ts,
      ("Definition has `assume` statement in body.",
      "Try to replace with `assert` and prove or add `{:axiom}`."))
  }

  lemma AllAssumptionsDescribed(ts: set<Tag>)
    requires IsAssumption(ts)
    ensures |AssumptionDescription(ts)| > 0
    {
    }

  function method RenderRow(begin: string, sep: string, end: string, cells: seq<string>): string {
    begin + Flatten(Seq.Interleave(sep, cells)) + end
  }

  function method IssueRow(a: Assumption, issue: string, mitigation: string): seq<string> {
      [ a.name
      , BoolYN(!(IsGhost in a.tags))
      , BoolYN(IsExplicitAssumption(a.tags))
      , BoolYN(HasExternAttribute in a.tags)
      , issue
      , mitigation
      ]
  }

  function method RenderAssumption(begin: string, sep: string, end: string, a: Assumption): string {
    var descs := AssumptionDescription(a.tags);
    var rows := Map((desc: (string, string)) =>
                  RenderRow(begin, sep, end, IssueRow(a, desc.0, desc.1)), descs);
    Flatten(Interleave("\n", rows))
  }

  function method RenderAssumptionMarkdown(a: Assumption): string {
    RenderAssumption("| ", " | ", " |", a)
  }

  function method RenderAuditReportMarkdown(r: Report): string {
    var header :=
      "|Name|Compiled|Explicit Assumption|Extern|Issue|Mitigation|\n" +
      "|----|--------|-------------------|------|-----|----------|\n";
    FoldL((s, a) => s + RenderAssumptionMarkdown(a) + "\n", header, r.assumptions)
  }

  function method RenderAssumptionHTML(a: Assumption): string {
    RenderAssumption("<tr><td>", "</td><td>", "</td></tr>", a)
  }

  function method RenderAuditReportHTML(r: Report): string {
    var header :=
      "<tr><th>Name</th><th>Compiled</th><th>Explicit Assumption</th>" +
      "<th>Extern</th><th>Issue</th><th>Mitigation</th></tr>\n";
    FoldL((s, a) => s + RenderAssumptionHTML(a) + "\n", header, r.assumptions)
  }

  function method RenderAssumptionText(a: Assumption): string {
    var descs := AssumptionDescription(a.tags);
    var lines := Map((desc: (string, string)) =>
      a.location.ToString() + ": " + a.name + ": " + desc.0 + " Possible mitigation: " + desc.1, descs);
    Flatten(Seq.Interleave("\n", lines))
  }

  function method RenderAuditReportText(r: Report): string {
    FoldL((s, a) => s + RenderAssumptionText(a) + "\n", "", r.assumptions)
  }
}

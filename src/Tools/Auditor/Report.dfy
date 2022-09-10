include "../../Utils/Library.dfy"

module AuditReport {
  import opened Utils.Lib.Seq

  //// Data types for report ////

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
    // TODO: decreases *?
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
    Assumption(name: string, tags: set<Tag>)

  datatype Report =
    Report(assumptions: seq<Assumption>)

  const EmptyReport := Report([])

  //// Tag categorization ////

  predicate method IsAssumption(ts: set<Tag>) {
    // This seems to be of little value at the moment
    // || (IsSubsetType in ts && MissingWitness in ts)
    || HasAxiomAttribute in ts
    || (&& IsCallable in ts
        && (|| (HasEnsuresClause in ts && (MissingBody in ts || HasExternAttribute in ts))
            || HasAssumeInBody in ts))
    // TODO: extern with no ensures but possibly empty type
  }

  predicate method IsExplicitAssumption(ts: set<Tag>) {
    HasAxiomAttribute in ts || HasAssumeInBody in ts
  }

  //// Report rendering ////

  function method BoolYN(b: bool): string {
    if b then "Y" else "N"
  }

  function method MaybeElt<T>(b: bool, elt: T): seq<T> {
     if b then [elt] else []
  }

  // TODO: improve these descriptions
  function method AssumptionDescription(ts: set<Tag>): seq<(string, string)> {
    MaybeElt(IsCallable in ts && MissingBody in ts && IsGhost in ts,
      ("Function or lemma has no body.",
       "Provide a body or add {:axiom}.")) +
    MaybeElt(IsCallable in ts && MissingBody in ts && !(IsGhost in ts),
      ("Callable definition has no body.",
       "Provide a body or add {:axiom}.")) +
    MaybeElt(HasExternAttribute in ts && HasRequiresClause in ts,
      ("Extern symbol with precondition.",
       "Extensively test client code.")) +
    MaybeElt(HasExternAttribute in ts && HasEnsuresClause in ts,
      ("Extern symbol with postcondition.",
       "Provide a model or a test case, or both.")) +
       /*
    MaybeElt(IsSubsetType in ts && MissingWitness in ts,
      ("Subset type has no witness and could be empty.",
       "Provide a witness.")) +
       */
    MaybeElt(HasAxiomAttribute in ts,
      ("Has explicit `{:axiom}` attribute.",
       "Attempt to provide a proof or model.")) +
    MaybeElt(HasAssumeInBody in ts,
      ("Has `assume` statement in body.",
      "Try to replace with `assert` and prove or add {:axiom}."))
  }

  lemma AllAssumptionsDescribed(ts: set<Tag>)
    requires IsAssumption(ts)
    ensures |AssumptionDescription(ts)| > 0
    {
    }

  function method RenderAssumptionMarkdown(a: Assumption): string {
    var descs := AssumptionDescription(a.tags);
    var issues := Map( (desc: (string, string)) => desc.0, descs);
    var mitigations := Map( (desc: (string, string)) => desc.1, descs);
    var cells :=
      [ a.name
      , BoolYN(!(IsGhost in a.tags))
      , BoolYN(IsExplicitAssumption(a.tags))
      , BoolYN(HasExternAttribute in a.tags)
      , Flatten(Seq.Interleave("<br>", issues))
      , Flatten(Seq.Interleave("<br>", mitigations))
      ];
    "| " + Flatten(Seq.Interleave(" | ", cells)) + " |"
  }

  function method RenderAuditReportMarkdown(r: Report): string {
    var header :=
      "|Name|Compiled|Explicit Assumption|Extern|Issue|Mitigation|\n" +
      "|----|--------|-------------------|------|-----|----------|\n";
    FoldL((s, a) => s + RenderAssumptionMarkdown(a) + "\n", header, r.assumptions)
  }
}

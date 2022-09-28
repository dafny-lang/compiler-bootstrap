include "Report.dfy"

module Bootstrap.Tools.AuditReportTest {

  import opened AuditReport
  import opened AST.Entities
  import opened AST.Locations
  import opened Utils.Lib.Datatypes

  method Main() {
    var loc := Location(Some("File.dfy"), 0, 0);
    var rpt := Report([
      Assumption("MinusBv8NoBody", loc,
        {IsCallable, IsGhost, MissingBody, HasEnsuresClause}),
      Assumption("LeftShiftBV128", loc,
        {IsCallable, IsGhost, MissingBody, HasEnsuresClause, HasAxiomAttribute}),
      Assumption("MinusBv8Assume", loc,
        {IsCallable, IsGhost, HasEnsuresClause, HasAssumeInBody}),
      Assumption("GenerateBytes", loc,
        {IsCallable, HasExternAttribute, HasEnsuresClause, MissingBody}),
      Assumption("GenerateBytesWithModel", loc,
        {IsCallable, HasExternAttribute, HasEnsuresClause}),
      Assumption("GenerateBytesWrapper", loc,
        {IsCallable, HasExternAttribute, HasEnsuresClause, HasAssumeInBody})
      /*
      Assumption("emptyType", loc,
        {IsSubsetType, MissingWitness})
        */
      // This doesn't pass IsAsssumption
      /*
      Assumption("WhoKnows", loc,
        {IsCallable, IsGhost, HasNoBody})
        */
      ]);
    assert forall a | a in rpt.assumptions :: IsAssumption(a.tags);
    var text := RenderAuditReportMarkdown(rpt);
    print text;
  }
}

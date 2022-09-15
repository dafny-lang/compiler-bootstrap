include "Report.dfy"

module AuditReportTest {

  import opened AuditReport

  method Main() {
    var rpt := Report([
      Assumption("MinusBv8NoBody",
        {IsCallable, IsGhost, MissingBody, HasEnsuresClause}),
      Assumption("LeftShiftBV128",
        {IsCallable, IsGhost, MissingBody, HasEnsuresClause, HasAxiomAttribute}),
      Assumption("MinusBv8Assume",
        {IsCallable, IsGhost, HasEnsuresClause, HasAssumeInBody}),
      Assumption("GenerateBytes",
        {IsCallable, HasExternAttribute, HasEnsuresClause, MissingBody}),
      Assumption("GenerateBytesWithModel",
        {IsCallable, HasExternAttribute, HasEnsuresClause}),
      Assumption("GenerateBytesWrapper",
        {IsCallable, HasExternAttribute, HasEnsuresClause, HasAssumeInBody})
      /*
      Assumption("emptyType",
        {IsSubsetType, MissingWitness})
        */
      // This doesn't pass IsAsssumption
      /*
      Assumption("WhoKnows",
        {IsCallable, IsGhost, HasNoBody})
        */
      ]);
    assert forall a | a in rpt.assumptions :: IsAssumption(a.tags);
    var text := RenderAuditReportMarkdown(rpt);
    print text;
  }
}

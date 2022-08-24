namespace Microsoft.Dafny;

public class AuditorPlugin : IRewriter {
  private readonly DafnyAuditor auditor = new();

  internal override void PostResolve(Program program) {
    var text = auditor.Audit(program);
    // TODO: write to the console or file depending on options
    Console.WriteLine(text);
  }
}

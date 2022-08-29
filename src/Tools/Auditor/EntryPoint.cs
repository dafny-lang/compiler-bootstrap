using System;
using Bootstrap.Tools.Auditor;

namespace Microsoft.Dafny.Compilers.SelfHosting.Auditor;

public class Auditor : Plugins.Rewriter {

  private readonly DafnyAuditor auditor = new();

  internal Auditor(ErrorReporter reporter) : base(reporter) { }

  public override void PostResolve(Program program) {
    var text = auditor.Audit(program);
    // TODO: write to the console or file depending on options
    Console.WriteLine(text);
  }
}

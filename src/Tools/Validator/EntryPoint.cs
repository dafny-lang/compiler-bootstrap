using System;
using Bootstrap.Tools.Validator.Validator;

namespace Microsoft.Dafny.Compilers.SelfHosting.Validator;

public class Validator : Plugins.Rewriter {
  public Validator(ErrorReporter reporter) : base(reporter) { }

  public override void PostResolve(Program program) {
    DafnyValidator.ValidateProgram(program);
  }
}

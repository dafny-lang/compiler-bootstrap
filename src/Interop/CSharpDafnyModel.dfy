include "CSharpModel.dfy"

module {:extern "Microsoft.BaseTypes"} {:compile false} Microsoft.BaseTypes {
  class {:extern} {:compile false} BigDec {}
}

module {:extern "Microsoft.Dafny"} {:compile false} Microsoft.Dafny {
  import System

  class {:extern} {:compile false} FreshIdGenerator {}
  class {:extern} {:compile false} Graph<T> {}
  class {:extern} {:compile false} Translator {}
  class {:extern} {:compile false} VisibilityScope {}
  class {:extern} {:compile false} ErrorReporter {}
  class {:extern} {:compile false} TypeConstraint {}
  class {:extern} {:compile false} BuiltIns {}
  trait {:extern} {:compile false} {:termination false} Cloner {}

  class {:extern} {:compile false} Resolver {}
  class {:extern "Resolver.TypeConstraint"} Resolver__TypeConstraint {}

  class {:extern} {:compile false} ConcreteSyntaxTree {
    // Changed return type of methods returning `this` to void (we lose chaining
    // but stop Dafny from complaining about missing return parameters when we
    // don't chain).
    method {:extern} Write(value: System.String)
    method {:extern} WriteLine(value: System.String)
    method {:extern} NewBlock(header: System.String) returns (wr: ConcreteSyntaxTree)
  }
}

module {:extern "Microsoft.Boogie"} {:compile false} Microsoft.Boogie {
  import System

  trait {:compile false} {:extern} {:termination false} IToken {
    var {:extern "filename"} FileName: System.String?
    var {:extern "line"} Line: System.int32
    var {:extern "col"} Column: System.int32
  }
  class {:extern} {:compile false} ErrorReporter {}
  class {:extern} {:compile false} Expr {}
  class {:extern} {:compile false} Function {}
}

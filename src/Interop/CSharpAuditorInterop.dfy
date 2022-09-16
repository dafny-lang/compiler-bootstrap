include "CSharpDafnyInterop.dfy"
include "CSharpInterop.dfy"

module {:extern "Microsoft.Dafny.Compilers.SelfHosting.Auditor"} {:compile false} Bootstrap.Tools.AuditorExterns {
  import System
  import Microsoft

  class {:compile false} Auditor {
    static method {:extern} Error(reporter: Microsoft.Dafny.ErrorReporter, file: System.String, line: System.int32, col: System.int32, msg: System.String)
    static method {:extern} Warning(reporter: Microsoft.Dafny.ErrorReporter, file: System.String, line: System.int32, col: System.int32, msg: System.String)
  }
}
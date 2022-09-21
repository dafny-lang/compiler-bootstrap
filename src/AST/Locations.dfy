/// Source code locations
/// =====================

include "../Interop/CSharpInterop.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Utils/Library.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Locations
{
  import System
  import Utils.Lib.Str
  import Microsoft.Dafny
  import opened Utils.Lib.Datatypes
  import opened Interop.CSharpDafnyInterop

  datatype Location =
    Location(file: Option<string>, line: nat, column: nat)
  {
    static function EMPTY(): Location {
      Location(None, 1, 0)
    }

    function ToString(): string {
      file.UnwrapOr("<none>") + "(" + Str.of_int(line) + "," + Str.of_int(column) + ")"
    }
  }

  class {:extern} ReporterAdapter {
    var r: Dafny.ErrorReporter;

    constructor(r: Dafny.ErrorReporter) {
      this.r := r;
    }

    method Message(
      src: Dafny.MessageSource, lvl: Dafny.ErrorLevel,
      loc: Location, msg: string
    ) {
      var file := if loc.file.Some? then StringUtils.ToCString(loc.file.value) else null;
      var line, col := TypeConv.ClampInt32(loc.line), TypeConv.ClampInt32(loc.column);
      var tok := TypeConv.CreateToken(file, line, col);
      var msg := StringUtils.ToCString(msg);
      r.Message(src, lvl, tok, msg);
    }
  }
}

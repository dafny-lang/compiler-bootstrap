/// Source code locations
/// =====================

include "../Interop/CSharpInterop.dfy"
include "../Utils/Library.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Locations
{
  import System
  import Utils.Lib.Str

  datatype Location =
    Location(file: string, line: System.int32, column: System.int32)
  {
    static function EMPTY(): Location {
      Location("<none>", 0, 0)
    }

    function ToString(): string {
      file + "(" + Str.of_int(line as int) + "," + Str.of_int(column as int) + ")"
    }
  }
}

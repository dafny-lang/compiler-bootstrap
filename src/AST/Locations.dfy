/// Source code locations
/// =====================

include "../Interop/CSharpInterop.dfy"
include "../Utils/Library.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Locations
{
  import System
  import Utils.Lib.Str
  import opened Utils.Lib.Datatypes

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
}

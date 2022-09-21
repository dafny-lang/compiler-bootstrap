include "Locations.dfy"
include "../Interop/CSharpDafnyInterop.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Translator.Location {
  import opened Interop.CSharpDafnyInterop
  import opened Locations

  function TranslateLocation(tok: Microsoft.Boogie.IToken): Location
    reads *
  {
    var filename := if tok.FileName == null then "<none>" else TypeConv.AsString(tok.FileName);
    var line := tok.Line as int;
    var col := tok.Column as int;
    Location(filename, line, col)
  }
}

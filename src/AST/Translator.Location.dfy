include "Locations.dfy"
include "../Utils/Library.dfy"
include "../Interop/CSharpDafnyInterop.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Translator.Location {
  import opened Interop.CSharpDafnyInterop
  import System
  import opened Locations
  import opened Utils.Lib.Datatypes

  function TranslateLocation(tok: Microsoft.Boogie.IToken): Location
    reads *
  {
    var fnOpt: Option<System.String> := OptionOfNullable(tok.FileName);
    Location(fnOpt.Map(s => TypeConv.AsString(s)), tok.Line as int, tok.Column as int)
  }
}

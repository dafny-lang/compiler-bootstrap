include "Locations.dfy"
include "../Utils/Library.dfy"
include "../Interop/CSharpDafnyInterop.dfy"

module {:options "-functionSyntax:4"} Bootstrap.AST.Translator.Location {
  import opened Interop.CSharpDafnyInterop
  import System
  import opened Locations
  import opened Utils.Lib.Math
  import opened Utils.Lib.Datatypes

  function TranslateLocation(tok: Microsoft.Boogie.IToken): Location
    reads *
  {
    var fnOpt: Option<System.String> :=
      if tok.FileName != null then Some(tok.FileName) else None;
    Location(
      fnOpt.Map(s => TypeConv.AsString(s)),
      Math.Max(tok.Line as int, 1),
      Math.Max(tok.Column as int, 0))
  }
}

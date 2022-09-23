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
    var fnOpt := OptionOfNullable(tok.FileName);
    Location(
      // FIXME: Using Option.Map leads to a type error in the compiled C# code
      if fnOpt.Some? then Some(TypeConv.AsString(fnOpt.value)) else None,
      Math.Max(tok.Line as int, 1),
      Math.Max(tok.Column as int, 0))
  }
}

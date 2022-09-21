include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Utils/Library.dfy"
include "Locations.dfy"
include "Syntax.dfy"
include "Translator.Location.dfy"

module Bootstrap.AST.Translator.Common {
  import opened Utils.Lib.Datatypes
  import opened Interop.CSharpDafnyInterop
  import C = Interop.CSharpDafnyASTModel
  import opened L = Location
  import Syntax.Debug

  datatype TranslationError =
    | Invalid(msg: string)
    | UnsupportedMember(decl: C.MemberDecl)
  {
    function method ToString() : string {
      match this
        case Invalid(msg) =>
          "Invalid term: " + msg
        case UnsupportedMember(decl) =>
          "Unsupported declaration: " + TypeConv.AnyToString(decl)
    }
  }

  type TranslationResult<+A> =
    Result<A, TranslationError>

  function method TranslateUnsupported(o: object?, descr: string)
    : (e: Debug.Unsupported)
    reads *
  {
    var loc :=
      if o is C.Statement then
        var s := o as C.Statement; TranslateLocation(s.Tok)
      else if o is C.Expression then
        var e := o as C.Expression; TranslateLocation(e.tok)
      else if o is C.UserDefinedType then
        var udt := o as C.UserDefinedType; TranslateLocation(udt.tok)
      else
        Locations.Location.EMPTY();
    Debug.Unsupported(TypeConv.AnyToString(o), descr, loc)
  }
}

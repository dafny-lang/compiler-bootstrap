include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Utils/Library.dfy"

module Bootstrap.AST.Translator.Common {
  import opened Utils.Lib.Datatypes
  import opened Interop.CSharpDafnyInterop
  import C = Interop.CSharpDafnyASTModel

  datatype TranslationError =
    | Invalid(msg: string)
    | UnsupportedMember(decl: C.MemberDecl)
  {
    function method ToString() : string {
      match this
        case Invalid(msg) =>
          "Invalid term: " + msg
        case UnsupportedMember(decl) =>
          "Unsupported declaration: " + TypeConv.ObjectToString(decl)
    }
  }

  type TranslationResult<+A> =
    Result<A, TranslationError>
}

include "../Interop/CSharpDafnyASTModel.dfy"
include "../Interop/CSharpDafnyInterop.dfy"
include "../Utils/Library.dfy"

module Bootstrap.AST.Translator.Common {
  import opened Utils.Lib.Datatypes
  import opened Interop.CSharpDafnyInterop
  import C = Interop.CSharpDafnyASTModel

  datatype TranslationError =
    | Invalid(msg: string)
    | GhostExpr(expr: C.Expression)
    | UnsupportedType(ty: C.Type)
    | UnsupportedExpr(expr: C.Expression)
    | UnsupportedStmt(stmt: C.Statement)
    | UnsupportedMember(decl: C.MemberDecl)
  {
    function method ToString() : string {
      match this
        case Invalid(msg) =>
          "Invalid term: " + msg
        case GhostExpr(expr) =>
          "Ghost expression: " + TypeConv.ObjectToString(expr)
        case UnsupportedType(ty) =>
          "Unsupported type: " + TypeConv.ObjectToString(ty)
        case UnsupportedExpr(expr) =>
          "Unsupported expression: " + TypeConv.ObjectToString(expr)
        case UnsupportedStmt(stmt) =>
          "Unsupported statement: " + TypeConv.ObjectToString(stmt)
        case UnsupportedMember(decl) =>
          "Unsupported declaration: " + TypeConv.ObjectToString(decl)
    }
  }

  type TranslationResult<+A> =
    Result<A, TranslationError>
}

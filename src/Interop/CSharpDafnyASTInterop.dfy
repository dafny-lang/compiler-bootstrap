include "CSharpDafnyASTModel.dfy"
include "CSharpModel.dfy"

module {:extern "CSharpDafnyASTInterop"} Bootstrap.Interop.CSharpDafnyASTInterop {
  import CSharpDafnyASTModel
  import System
  import opened System.Collections.Generic

  function {:axiom} TypeHeight(t: CSharpDafnyASTModel.Type) : nat

  function {:axiom} ASTHeight(c: object) : nat
    requires || c is CSharpDafnyASTModel.Expression
             || c is CSharpDafnyASTModel.Statement
             || c is CSharpDafnyASTModel.Declaration
             || c is CSharpDafnyASTModel.ModuleDefinition
             || c is CSharpDafnyASTModel.Attributes

  class {:extern} TypeUtils {
    constructor {:extern} () requires false // Prevent instantiation

    static function method {:extern} NormalizeExpand(ty: CSharpDafnyASTModel.Type)
      : (ty': CSharpDafnyASTModel.Type)
      ensures TypeHeight(ty') <= TypeHeight(ty)
  }

  class {:extern} ExprUtils {
    constructor {:extern} () requires false // Prevent instantiation

    static function method {:extern} UnescapedCharacters(e: CSharpDafnyASTModel.LiteralExpr)
      : (cs: List<char>)
      reads e
      requires e.Value is System.String
  }
}

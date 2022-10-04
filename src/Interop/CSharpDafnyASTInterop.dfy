include "CSharpDafnyModel.dfy"
include "CSharpModel.dfy"

module {:extern "CSharpDafnyASTInterop"} Bootstrap.Interop.CSharpDafnyASTInterop {
  import System
  import Microsoft.Dafny
  import opened System.Collections.Generic

  function {:axiom} ASTHeight(c: object?) : nat
    requires || c is Dafny.Type?
             || c is Dafny.Expression?
             || c is Dafny.Statement?
             || c is Dafny.Declaration?
             || c is Dafny.ModuleDefinition?
             || c is Dafny.Attributes?

  class {:extern} TypeUtils {
    constructor {:extern} () requires false // Prevent instantiation

    static function method {:extern} NormalizeExpand(ty: Dafny.Type)
      : (ty': Dafny.Type)
      ensures ASTHeight(ty') <= ASTHeight(ty)
  }

  class {:extern} ExprUtils {
    constructor {:extern} () requires false // Prevent instantiation

    static function method {:extern} UnescapedCharacters(e: Dafny.LiteralExpr)
      : (cs: List<char>)
      reads e
      requires e.Value is System.String
  }
}

namespace CSharpDafnyASTInterop {
  public partial class TypeUtils {
    public static Microsoft.Dafny.Type NormalizeExpand(Microsoft.Dafny.Type ty) =>
      ty.NormalizeExpand();
  }
  public partial class ExprUtils {
    public static IEnumerable<char> UnescapedCharacters(Microsoft.Dafny.CharLiteralExpr e) =>
      Microsoft.Dafny.Util.UnescapedCharacters((string)e.Value, false);
  }
}

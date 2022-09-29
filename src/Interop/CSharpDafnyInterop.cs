using System.Numerics;

namespace CSharpDafnyInterop {
  public partial class StringUtils {
    public static string ToCString(Dafny.ISequence<char> s) {
      // Interning guarantees that this behaves like a "function method" in Dafny
      return string.Intern(s.ToString() ?? "null");
    }

    public static Dafny.ISequence<char> OfCString(string s) {
      return Dafny.Sequence<char>.FromString(s);
    }
  }

  public partial class TypeConv {
    public static readonly BigInteger ONE = new BigInteger(1);
    public static readonly BigInteger TEN = new BigInteger(10);

    // System.Boolean to Dafny bool (Dafny thinks them different)
    public static bool AsBool(System.Boolean o) => o;
    // System.Numerics.BigInteger to Dafny int (Dafny thinks them different)
    public static System.Numerics.BigInteger AsInt(System.Numerics.BigInteger o) => o;
    // System.String to Dafny string (these are actually different)
    public static Dafny.ISequence<char> AsString(System.String o) =>
      StringUtils.OfCString(o);
    // BigDec to Dafny real (these are actually different)
    public static Dafny.BigRational AsReal(Microsoft.BaseTypes.BigDec o) {
      if (o.Exponent >= 0) {
        return new Dafny.BigRational(o.Mantissa * BigInteger.Pow(TEN, o.Exponent), 1);
      } else {
        return new Dafny.BigRational(o.Mantissa, BigInteger.Pow(TEN, -o.Exponent));
      }
    }

    public static BigInteger Numerator(Dafny.BigRational r) => r.num;
    public static BigInteger Denominator(Dafny.BigRational r) => r.den;

    public static Dafny.ISequence<char> AnyToString(object? o) =>
      AsString(o is null ? "null" : o.ToString());
  }

  public static Boogie.IToken CreateToken(System.String file, int line, int col) {
    var tok = new Token(line, col);
    tok.Filename = filename;
    return tok;
  }
}

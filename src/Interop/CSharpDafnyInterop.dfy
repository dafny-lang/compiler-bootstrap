include "CSharpModel.dfy"
include "CSharpDafnyModel.dfy"
include "CSharpInterop.dfy"

module {:extern "CSharpDafnyInterop"} Bootstrap.Interop.CSharpDafnyInterop {
  import Microsoft
  import Microsoft.Dafny
  import Microsoft.Boogie
  import opened CSharpInterop

  class {:extern} StringUtils {
    constructor {:extern} () requires false // Prevent instantiation

    static function method {:extern} ToCString(s: string) : System.String
    static function method {:extern} OfCString(s: System.String) : string
  }

  class {:extern} TypeConv {
    constructor {:extern} () requires false // Prevent instantiation

    static function method {:extern} AsBool(o: System.Boolean) : bool
    static function method {:extern} AsInt(o: System.Numerics.BigInteger) : int
    static function method {:extern} AsReal(o: Microsoft.BaseTypes.BigDec) : real
    static function method {:extern} AsString(o: System.String) : string

    static function method {:extern} Numerator(r: real) : int
    static function method {:extern} Denominator(r: real) : int

    static function method AsIntegerRatio(r: real) : (int, int) {
      (TypeConv.Numerator(r), TypeConv.Denominator(r))
    }

    static function method {:extern} ObjectToString(o: object?) : string

    static function method ClampInt32(x: int): System.int32 {
      if x < -0x7fff_ffff then -0x7fff_ffff
      else if x > 0x7fff_ffff then 0x7fff_ffff
      else x as System.int32
    }

    static method {:extern} CreateToken(file: System.String?, line: System.int32, col: System.int32)
      returns (tok: Boogie.IToken)
      ensures fresh(tok)
  }

  class SyntaxTreeAdapter {
    var wr: Microsoft.Dafny.ConcreteSyntaxTree

    constructor(wr: Microsoft.Dafny.ConcreteSyntaxTree) {
      this.wr := wr;
    }

    method Write(value: string) {
      wr.Write(StringUtils.ToCString(value));
    }

    method WriteLine(value: string) {
      wr.WriteLine(StringUtils.ToCString(value));
    }

    method NewBlock(header: string) returns (st': SyntaxTreeAdapter) {
      var wr' := wr.NewBlock(StringUtils.ToCString(header));
      st' := new SyntaxTreeAdapter(wr');
    }
  }
}

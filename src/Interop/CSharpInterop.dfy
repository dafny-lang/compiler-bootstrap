include "CSharpModel.dfy"

module {:extern "CSharpInterop"} Bootstrap.Interop.CSharpInterop {
  import System
  import opened System.Collections.Generic

  class ListUtils {
    constructor {:extern} () requires false // Prevent instantiation

    static function method {:extern} FoldR<A, B>(f: (A, B) -> B, b0: B, l: List<A>) : B

    static method {:extern} Mk<T>() returns (l: List<T>)
    static method {:extern} Append<T>(l: List<T>, t: T)

    static function method {:extern} DictionaryToList<K, V>(d: Dictionary<K, V>): List<(K, V)>

    static function method ToSeq<T>(l: List<T>) : seq<T> {
      FoldR((t, s) => [t] + s, [], l)
    }

    static method AppendSeq<T>(l: List<T>, s:seq<T>) {
      var i := 0;
      while (i < |s|) {
        Append(l, s[i]);
        i := i + 1;
      }
    }
  }
}

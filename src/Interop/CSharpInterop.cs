#nullable enable
using System.Numerics;

namespace CSharpInterop {
  public partial class ListUtils {
    public static List<T> Mk<T>() => new List<T>();

    public static void Append<T>(List<T> l, T t) => l.Add(t);

    public static B FoldL<A, B>(Func<B, A, B> f, B b0, List<A>? lA) {
      if(lA is null) {
        return b0;
      }
      for (int i = 0; i < lA.Count; i++) {
        b0 = f(b0, lA[i]);
      }
      return b0;
    }

    public static B FoldR<A, B>(Func<A, B, B> f, B b0, List<A>? lA) {
      if(lA is null) {
        return b0;
      }
      for (int i = lA.Count - 1; i >= 0; i--) {
        b0 = f(lA[i], b0);
      }
      return b0;
    }
  }

  public partial class EnumerableUtils {
    public static B FoldR<A, B>(Func<A, B, B> f, B b0, IEnumerable<A>? eA) {
      if(eA is null) {
        return b0;
      }
      foreach (var x in eA) {
        b0 = f(x, b0);
      }
      return b0;
    }
  }

  public partial class DictUtils {
    public static R FoldL<K, V, R>(Func<R, K, V, R> f, R r0, Dictionary<K, V>? d) where K : notnull {
      if(d is null) {
        return r0;
      }
      var keys = d.Keys.ToList();
      // The keys really should be sorted to make this a valid `function`
      // in Dafny, but some of the instances that come up in practice have
      // key types that don't implement `IComparable`. *sigh*
      //keys.Sort();
      foreach (var k in keys) {
        r0 = f(r0, k, d[k]);
      }
      return r0;
    }
  }
}

module Utils.Lib.ControlFlow {
  function method Unreachable<A>() : A
    requires false
  {
    match () {}
  }
}

module Utils.Lib.Debug {
  class {:compile false} Debugger {
    static method {:extern "System.Diagnostics.Debugger", "Break"} Break() {}
  }

  function TODO<A>(a : A) : A {
    a
  } by method {
    Debugger.Break();
    return a;
  }
}

module Utils.Lib.Datatypes {
  datatype Option<+T> = | Some(value: T) | None
  {
    function method UnwrapOr(default: T) : T {
      if this.Some? then value else default
    }

    function method ToSuccessOr<E>(f: E): Result<T, E> {
      match this
        case Some(v) => Success(v)
        case None() => Failure(f)
    }
  }

  datatype Result<+T, +R> = | Success(value: T) | Failure(error: R) {
    predicate method IsFailure() {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U, R>
      requires Failure?
    {
      Failure(this.error)
    }

    function method Extract(): T
      requires Success?
    {
      value
    }

    // FIXME: Port
    function method MapFailure<R'>(f: R --> R') : Result<T, R'>
      requires this.Failure? ==> f.requires(this.error)
    {
      match this
        case Success(value) => Success(value)
        case Failure(error) => Failure(f(error))
    }

    function method Then<K>(f: T --> Result<K, R>) : Result<K, R>
      requires Success? ==> f.requires(value)
    {
      match this
        case Success(value) => f(value)
        case Failure(err) => Failure(err)
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E)
  {
    predicate method IsFailure() {
      Fail?
    }
    // Note: PropagateFailure returns a Result, not an Outcome.
    function method PropagateFailure<U>(): Result<U, E>
      requires Fail?
    {
      Failure(this.error)
    }
    // Note: no Extract method
  }

  // A helper function to ensure a requirement is true at runtime
  // :- Need(5 == |mySet|, "The set MUST have 5 elements.")
  // FIXME: Move to library (added opaque)
  function method {:opaque} Need<E>(condition: bool, error: E): (result: Outcome<E>)
    ensures condition <==> result.Pass?
  {
    if condition then Pass else Fail(error)
  }
}

module Utils.Lib.Seq {
  // FIXME why not use a comprehension directly?
  // FIXME move `f`
  function method {:opaque} Map<T, Q>(f: T ~> Q, ts: seq<T>) : (qs: seq<Q>)
    reads f.reads
    requires forall t | t in ts :: f.requires(t)
    ensures |qs| == |ts|
    ensures forall i | 0 <= i < |ts| :: qs[i] == f(ts[i])
    ensures forall q | q in qs :: exists t | t in ts :: q == f(t)
  {
    if ts == [] then [] else [f(ts[0])] + Map(f, ts[1..])
  }

  function method FoldL<TAcc(!new), T>(f: (TAcc, T) ~> TAcc, a0: TAcc, ts: seq<T>) : TAcc
    reads f.reads
    requires forall a, t | t in ts :: f.requires(a, t)
  {
    if ts == [] then a0 else FoldL(f, f(a0, ts[0]), ts[1..])
  }

  lemma FoldL_induction'<TAcc(!new), T>(
    f: (TAcc, T) ~> TAcc, a0: TAcc, ts: seq<T>,
    prefix: seq<T>, P: (TAcc, seq<T>) -> bool
  )
    requires forall a, t | t in ts :: f.requires(a, t)
    requires P(a0, prefix)
    requires forall a, t, ts' | t in ts && P(a, ts') :: P(f(a, t), ts' + [t])
    ensures P(FoldL(f, a0, ts), prefix + ts)
  {
    if ts == [] {
      assert prefix + ts == prefix;
    } else {
      var t0, ts' := ts[0], ts[1..];
      var a0' := f(a0, t0);
      var prefix' := prefix + [t0];
      FoldL_induction'(f, a0', ts[1..], prefix', P);
      assert P(FoldL(f, a0', ts[1..]), prefix' + ts');
      assert prefix' + ts' == prefix + ts;
    }
  }

  lemma FoldL_induction<TAcc(!new), T>(
    f: (TAcc, T) ~> TAcc, a0: TAcc, ts: seq<T>,
    P: (TAcc, seq<T>) -> bool
  )
    requires forall a, t | t in ts :: f.requires(a, t)
    requires P(a0, [])
    requires forall a, t, ts' | t in ts && P(a, ts') :: P(f(a, t), ts' + [t])
    ensures P(FoldL(f, a0, ts), ts)
  {
    assert [] + ts == ts;
    FoldL_induction'(f, a0, ts, [], P);
  }

  function method FoldR<TAcc(!new), T>(f: (TAcc, T) ~> TAcc, a0: TAcc, ts: seq<T>) : TAcc
    reads f.reads
    requires forall a, t | t in ts :: f.requires(a, t)
  {
    if ts == [] then a0 else f(FoldL(f, a0, ts[1..]), ts[0])
  }

  function method Flatten<T>(tss: seq<seq<T>>): (ts: seq<T>)
    ensures forall s <- ts :: exists ts <- tss :: s in ts
    ensures forall ts0 <- tss, s <- ts0 :: s in ts
  {
    if tss == [] then []
    else tss[0] + Flatten(tss[1..])
  }

  // TODO: Why not use forall directly?
  function method {:opaque} All<T>(P: T ~> bool, ts: seq<T>) : (b: bool)
    reads P.reads
    requires forall t | t in ts :: P.requires(t)
    ensures b == forall t | t in ts :: P(t)
    ensures b == forall i | 0 <= i < |ts| :: P(ts[i])
  {
    if ts == [] then true else P(ts[0]) && All(P, ts[1..])
  }

  lemma All_weaken<T>(P: T ~> bool, Q: T~> bool, ts: seq<T>)
    requires forall t | t in ts :: P.requires(t)
    requires forall t | t in ts :: Q.requires(t)
    requires forall t | t in ts :: P(t) ==> Q(t)
    ensures All(P, ts) ==> All(Q, ts)
  {}

  lemma All_weaken_auto<T>(ts: seq<T>)
    ensures forall P: T ~> bool, Q: T ~> bool |
      && (forall t: T | t in ts :: P.requires(t))
      && (forall t: T | t in ts :: Q.requires(t))
      && (forall t: T | t in ts :: P(t) ==> Q(t)) ::
     All(P, ts) ==> All(Q, ts)
  {}

  import Math

  function method {:opaque} Max(s: seq<int>, default: int) : (m: int)
    requires forall i | i in s :: default <= i
    ensures if s == [] then m == default else m in s
    ensures forall i | i in s :: i <= m
    ensures default <= m
  {
    var P := (m, s) =>
      && (if s == [] then m == default else m in s)
      && (forall i | i in s :: i <= m);
    FoldL_induction(Math.Max, default, s, P);
    FoldL(Math.Max, default, s)
  }

  function method {:opaque} MaxF<T>(f: T ~> int, ts: seq<T>, default: int) : (m: int)
    reads f.reads
    requires forall t | t in ts :: f.requires(t)
    requires forall t | t in ts :: default <= f(t)
    ensures if ts == [] then m == default else exists t | t in ts :: f(t) == m
    ensures forall t | t in ts :: f(t) <= m
    ensures default <= m
  {
    var s := Map(f, ts);
    var m := Max(s, default);
    assert forall t | t in ts :: f(t) <= m by {
      forall t | t in ts ensures f(t) <= m { assert f(t) in s; }
    }
    m
  }

  function method {:opaque} Zip<T, Q>(ts: seq<T>, qs: seq<Q>)
    : (tqs: seq<(T, Q)>)
    requires |ts| == |qs|
    ensures |ts| == |tqs| == |qs|
    ensures forall i | 0 <= i < |tqs| :: tqs[i] == (ts[i], qs[i])
    ensures forall tq | tq in tqs :: tq.0 in ts && tq.1 in qs
  {
    if ts == [] then []
    else [(ts[0], qs[0])] + Zip(ts[1..], qs[1..])
  }

  // TODO: Merge.  Removed unnecessary trigger and strengthened postcondition
  function method {:opaque} Filter<T>(s: seq<T>, f: (T ~> bool)): (result: seq<T>)
    requires forall i | 0 <= i < |s| :: f.requires(s[i])
    ensures |result| <= |s| // DISCUSS: This allows duplication / unifiqation
    ensures forall x | x in result :: f.requires(x) && x in s && f(x)
    ensures forall x | x in s && f(x) :: x in result
    reads f.reads
  {
    if |s| == 0 then []
    else (if f(s[0]) then [s[0]] else []) + Filter(s[1..], f)
  }

  import Datatypes

  function method {:opaque} MapResult<T, Q, E>(ts: seq<T>, f: T ~> Datatypes.Result<Q, E>)
    : (qs: Datatypes.Result<seq<Q>, E>)
    reads f.reads
    requires forall t | t in ts :: f.requires(t)
    decreases ts
    ensures qs.Success? ==> |qs.value| == |ts|
    ensures qs.Success? ==> forall i | 0 <= i < |ts| :: f(ts[i]).Success? && qs.value[i] == f(ts[i]).value
    ensures qs.Failure? ==> exists i | 0 <= i < |ts| :: f(ts[i]).Failure? && qs.error == f(ts[i]).error
  {
    if ts == [] then
      Datatypes.Success([])
    else
      var hd :- f(ts[0]);
      var tl :- MapResult(ts[1..], f);
      Datatypes.Success([hd] + tl)
  }

  function method FoldLResult<TAcc(!new), T, TErr>(f: (TAcc, T) ~> Datatypes.Result<TAcc, TErr>, a0: TAcc, ts: seq<T>)
    : (acc: Datatypes.Result<TAcc, TErr>)
    reads f.reads
    requires forall a, t | t in ts :: f.requires(a, t)
  {
    if ts == [] then Datatypes.Success(a0)
    else
      var a0 :- f(a0, ts[0]);
      FoldLResult(f, a0, ts[1..])
  }

  function method {:opaque} MapFilter<T, Q>(s: seq<T>, f: (T ~> Datatypes.Option<Q>)): (result: seq<Q>)
    requires forall i | 0 <= i < |s| :: f.requires(s[i])
    ensures |result| <= |s|
    ensures forall y | y in result :: exists x | x in s :: f.requires(x) && f(x) == Datatypes.Some(y)
    ensures forall x | x in s && f(x).Some? :: f(x).value in result
    reads f.reads
  {
    if |s| == 0 then []
    else (match f(s[0])
            case Some(y) => [y]
            case None => []) + MapFilter(s[1..], f)
  }
}

module Utils.Lib.Outcome.OfSeq { // FIXME rename to Seq
  import Seq
  import opened Datatypes

  function method Combine<E>(so: seq<Outcome<E>>): (os: Outcome<seq<E>>)
    ensures os.Pass? <==> forall o | o in so :: o.Pass?
  {
    var fails := Seq.Filter(so, (x: Outcome<E>) => x.Fail?);
    if |fails| == 0 then
      Pass
    else
      assert fails[0] in so;
      Fail(Seq.Map((x: Outcome<E>) requires x.Fail? => x.error, fails))
  }

  function method CombineSeq<E>(so: seq<Outcome<seq<E>>>): (os: Outcome<seq<E>>)
    ensures os.Pass? <==> forall o | o in so :: o.Pass?
  {
    var fails := Seq.Filter(so, (x: Outcome<seq<E>>) => x.Fail?);
    if |fails| == 0 then
      Pass
    else
      assert fails[0] in so;
      Fail(Seq.Flatten(Seq.Map((x: Outcome<seq<E>>) requires x.Fail? => x.error, fails)))
  }
}

module Utils.Lib.Str {
module Private {
  function method digits(n: int, base: int): (digits: seq<int>)
    requires base > 1
    requires n >= 0
    decreases n
    ensures forall d | d in digits :: 0 <= d < base
  {
    if n == 0 then
      []
    else
      assert n > 0;
      assert base > 1;
      assert n < base * n;
      assert n / base < n;
      digits(n / base, base) + [n % base]
  }

  function method string_of_digits(digits: seq<int>, chars: seq<char>) : string
    requires forall d | d in digits :: 0 <= d < |chars|
  {
    if digits == [] then ""
    else
      assert digits[0] in digits;
      assert forall d | d in digits[1..] :: d in digits;
      [chars[digits[0]]] + string_of_digits(digits[1..], chars)
  }
}

  function method of_int_any(n: int, chars: seq<char>) : string
    requires |chars| > 1
  {
    var base := |chars|;
    if n == 0 then
      "0"
    else if n > 0 then
      Private.string_of_digits(Private.digits(n, base), chars)
    else
      "-" + Private.string_of_digits(Private.digits(-n, base), chars)
  }

  const HEX_DIGITS := [
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
    'A', 'B', 'C', 'D', 'E', 'F']

  // FIXME rename
  function method of_int(n: int, base: int := 10) : string
    requires 2 <= base <= 16
  {
    of_int_any(n, HEX_DIGITS[..base])
  }

  method Test() { // FIXME {:test}?
    expect of_int(0, 10) == "0";
    expect of_int(3, 10) == "3";
    expect of_int(302, 10) == "302";
    expect of_int(-3, 10) == "-3";
    expect of_int(-302, 10) == "-302";
  }

  function method of_bool(b: bool) : string {
    if b then "true" else "false"
  }

  function method of_char(c: char) : string {
    [c]
  }

  function method Join(sep: string, strs: seq<string>) : string {
    if |strs| == 0 then ""
    else if |strs| == 1 then strs[0]
    else strs[0] + sep + Join(sep, strs[1..])
  }

  function method Concat(strs: seq<string>) : string {
    Join("", strs)
  }
}

module Utils.Lib.Set {
  function method Map<T, T'>(ts: set<T>, f: T ~> T'): set<T'>
    reads set t <- ts, o <- f.reads(t) :: o
    requires forall t <- ts :: f.requires(t)
  {
    set t <- ts :: f(t)
  }

  function method OfSeq<T(==)>(sq: seq<T>): set<T> {
    set x <- sq
  }

  function method OfSlice<T(==)>(arr: array<T>, lo: int, hi: int): set<T>
    requires 0 <= lo <= hi <= arr.Length
    reads arr
  {
    OfSeq(arr[lo..hi])
  }

  function method OfArray<T(==)>(arr: array<T>): set<T>
    reads arr
  {
    OfSlice(arr, 0, arr.Length)
  }
}

module Utils.Lib.Multiset {
  function method OfSlice<T(==)>(arr: array<T>, lo: int, hi: int): multiset<T>
    requires 0 <= lo <= hi <= arr.Length
    reads arr
  {
    multiset(arr[lo..hi])
  }

  function method OfArray<T(==)>(arr: array<T>): multiset<T>
    reads arr
  {
    OfSlice(arr, 0, arr.Length)
  }
}

module Utils.Lib.Array {
  import Set
  import Multiset

  method OfSet<T>(st: set<T>) returns (arr: array<T>)
    ensures fresh(arr)
    ensures Set.OfArray(arr) == st
    ensures Multiset.OfArray(arr) == multiset(st)
  {
    if |st| == 0 {
      arr := new T[|st|];
    } else {
      var s := st;
      var t0 :| t0 in s;
      arr := new T[|st|](_ => t0);
      for i := 0 to |s|
        invariant |s| == |st| - i
        invariant Set.OfSlice(arr, 0, i) + s == st
        invariant Multiset.OfSlice(arr, 0, i) + multiset(s) == multiset(st)
      {
        var t :| t in s;
        arr[i] := t;
        s := s - {t};
        assert Set.OfSlice(arr, 0, i + 1) == Set.OfSlice(arr, 0, i) + {t};
      }
    }
  }
}

module Utils.Lib.Int.Comparison {
  import C = Sort.Comparison

  function method Cmp(i0: int, i1: int): C.Cmp {
    if i0 < i1 then C.Lt
    else if i0 > i1 then C.Gt
    else C.Eq
  }

  const Comparison := C.Comparison(Cmp);

  lemma {:induction ints} Total(ints: set<int>)
    ensures Comparison.Total?(ints)
  {}
}

module Utils.Lib.Char.Comparison {
  import C = Sort.Comparison

  function method Cmp(i0: char, i1: char): C.Cmp {
    if i0 < i1 then C.Lt
    else if i0 > i1 then C.Gt
    else C.Eq
  }

  const Comparison := C.Comparison(Cmp);

  lemma {:induction chars} Total(chars: set<char>)
    ensures Comparison.Total?(chars)
  {}
}

module Utils.Lib.Seq.Comparison {
  import Set
  import C = Sort.Comparison

  function Flatten<T>(tss: set<seq<T>>): set<T> {
    set ts <- tss, t <- ts :: t
  }

  datatype SeqComparison<!T> = SeqComparison(cmp: C.Comparison<T>) {
    function method Cmp(s0: seq<T>, s1: seq<T>): C.Cmp {
      if s0 == [] && s1 == [] then C.Eq
      else if s0 == [] then C.Lt
      else if s1 == [] then C.Gt
      else
        match cmp.Compare(s0[0], s1[0])
          case Eq => Cmp(s0[1..], s1[1..])
          case other => other
    }

    const Comparison := C.Comparison(Cmp);

    lemma {:induction false} Complete1(s0: seq<T>, s1: seq<T>)
      requires cmp.Total?(Set.OfSeq(s0) + Set.OfSeq(s1))
      ensures Comparison.Complete??(s0, s1)
    {
      if s0 != [] && s1 != [] {
        assert s0[0] in s0 && s1[0] in s1;
        assert s0[0] in Set.OfSeq(s0) && s1[0] in Set.OfSeq(s1);
        Complete1(s0[1..], s1[1..]);
      }
    }

    lemma {:induction false} Antisymmetric1(s0: seq<T>, s1: seq<T>)
      requires cmp.Total?(Set.OfSeq(s0) + Set.OfSeq(s1))
      ensures Comparison.Antisymmetric??(s0, s1)
    {
      // forall s0, s1 | s0 in tss && s1 in tss ensures Comparison.Complete??(s0, s1) {
      if s0 != [] && s1 != [] {
        assert s0[0] in s0 && s1[0] in s1;
        assert s0[0] in Set.OfSeq(s0) && s1[0] in Set.OfSeq(s1);
        assert s0 == [s0[0]] + s0[1..] && s1 == [s1[0]] + s1[1..];
        Antisymmetric1(s0[1..], s1[1..]);
      }
    }

    lemma {:induction false} Transitive1(s0: seq<T>, s1: seq<T>, s2: seq<T>)
      requires cmp.Total?(Set.OfSeq(s0) + Set.OfSeq(s1) + Set.OfSeq(s2))
      ensures Comparison.Transitive??(s0, s1, s2)
    {
      if s0 != [] && s1 != [] && s1 != [] && Comparison.Compare(s0, s1).Le? && Comparison.Compare(s1, s2).Le? {
        assert s0[0] in s0 && s1[0] in s1 && s2[0] in s2;
        assert s0[0] in Set.OfSeq(s0) && s1[0] in Set.OfSeq(s1) && s2[0] in Set.OfSeq(s2);
        assert s0 == [s0[0]] + s0[1..] && s1 == [s1[0]] + s1[1..] && s2 == [s2[0]] + s2[1..];
        assert cmp.Compare(s0[0], s1[0]).Le?;
        assert cmp.Compare(s1[0], s2[0]).Le?;
        assert cmp.Transitive??(s0[0], s1[0], s2[0]);
        assert cmp.Compare(s0[0], s2[0]).Le?;
        Transitive1(s0[1..], s1[1..], s2[1..]);
      }
    }

    lemma {:induction false} Total(tss: set<seq<T>>)
      requires cmp.Total?(Flatten(tss))
      ensures Comparison.Total?(tss)
    {
      forall s0, s1 | s0 in tss && s1 in tss ensures Comparison.Complete??(s0, s1) {
        Complete1(s0, s1);
      }
      forall s0, s1 | s0 in tss && s1 in tss ensures Comparison.Antisymmetric??(s0, s1) {
        Antisymmetric1(s0, s1);
      }
      forall s0, s1, s2 | s0 in tss && s1 in tss && s2 in tss ensures Comparison.Transitive??(s0, s1, s2) {
        Transitive1(s0, s1, s2);
      }
    }
  }
}

module Utils.Lib.Str.Comparison {
  import C = Sort.Comparison
  import SeqCmp = Seq.Comparison
  import CharCmp = Char.Comparison

  const StrComparison := SeqCmp.SeqComparison(CharCmp.Comparison);
  const Comparison := StrComparison.Comparison;

  lemma {:induction false} Total(strs: set<string>)
    ensures Comparison.Total?(strs)
  {
    CharCmp.Total(SeqCmp.Flatten(strs));
    StrComparison.Total(strs);
  }
}

module Utils.Lib.Math {
  function method {:opaque} Max(x: int, y: int) : (m: int)
    ensures x <= m
    ensures y <= m
    ensures x == m || y == m
  {
    if (x <= y) then y else x
  }

  function method {:opaque} IntPow(x: int, n: nat) : int {
    if n == 0 then 1
    else x * IntPow(x, n - 1)
  }
}

module Utils.Lib.Sort.Comparison {
  import opened Datatypes

  datatype Cmp = Lt | Eq | Gt {
    function method Flip(): Cmp {
      match this
        case Lt => Gt
        case Eq => Eq
        case Gt => Lt
    }

    const Le? := this != Gt
    const Ge? := this != Lt

    static function method ComputeTransitivity(c0: Cmp, c1: Cmp): Option<Cmp> {
      match (c0, c1)
        case (Lt, Lt) => Some(Lt)
        case (Lt, Eq) => Some(Lt)
        case (Lt, Gt) => None
        case (Eq, Lt) => Some(Lt)
        case (Eq, Eq) => Some(Eq)
        case (Eq, Gt) => Some(Gt)
        case (Gt, Lt) => None
        case (Gt, Eq) => Some(Gt)
        case (Gt, Gt) => Some(Gt)
    }
  }

  datatype Comparison<!T> = Comparison(cmp: (T, T) -> Cmp) {
    function method Compare(t0: T, t1: T): Cmp {
      cmp(t0, t1)
    }

    predicate Complete??(t0: T, t1: T) {
      cmp(t0, t1) == cmp(t1, t0).Flip()
    }

    predicate Antisymmetric??(t0: T, t1: T) {
      cmp(t0, t1) == Eq ==> t0 == t1
    }

    predicate Transitive??(t0: T, t1: T, t2: T) {
      cmp(t0, t1).Le? && cmp(t1, t2).Le? ==> cmp(t0, t2).Le?
    }

    predicate Reflexive??(t0: T) {
      cmp(t0, t0) == Eq
    }

    lemma AlwaysReflexive(t0: T)
      requires Complete??(t0, t0)
      ensures Reflexive??(t0)
    {}

    lemma PreciselyTransitive'(t0: T, t1: T, t2: T)
      requires Complete??(t0, t1) && Complete??(t0, t2) && Complete??(t1, t2)
      requires Antisymmetric??(t0, t1) && Antisymmetric??(t0, t2) && Antisymmetric??(t1, t2)
      requires Transitive??(t0, t1, t2) && Transitive??(t1, t2, t0)
      requires cmp(t0, t1).Le? && cmp(t1, t2).Le?
      ensures Cmp.ComputeTransitivity(cmp(t0, t1), cmp(t1, t2)) == Some(cmp(t0, t2))
    {}

    lemma PreciselyTransitive(t0: T, t1: T, t2: T)
      requires Reflexive??(t0) && Reflexive??(t1) && Reflexive??(t2)
      requires Complete??(t0, t1) && Complete??(t0, t2) && Complete??(t1, t2)
      requires Antisymmetric??(t0, t1) && Antisymmetric??(t0, t2) && Antisymmetric??(t1, t2)
      requires Transitive??(t0, t1, t2) && Transitive??(t1, t2, t0)
      requires Transitive??(t2, t1, t0) && Transitive??(t1, t0, t2)
      ensures match Cmp.ComputeTransitivity(cmp(t0, t1), cmp(t1, t2))
        case Some(c12) => c12 == cmp(t0, t2)
        case None => true
    {
      match (cmp(t0, t1), cmp(t1, t2))
        case (Lt, Lt) | (Lt, Eq) | (Eq, Lt) | (Eq, Eq) =>
          PreciselyTransitive'(t0, t1, t2);
        case (Eq, Gt) | (Gt, Eq) | (Gt, Gt) =>
          PreciselyTransitive'(t2, t1, t0);
        case (Lt, Gt) | (Gt, Lt) =>
    }

    predicate Complete?(ts: set<T>) {
      forall t0, t1 | t0 in ts && t1 in ts :: Complete??(t0, t1)
    }

    predicate Antisymmetric?(ts: set<T>) {
      forall t0, t1 | t0 in ts && t1 in ts :: Antisymmetric??(t0, t1)
    }

    predicate Transitive?(ts: set<T>) {
      forall t0, t1, t2 | t0 in ts && t1 in ts && t2 in ts :: Transitive??(t0, t1, t2)
    }

    predicate Valid?(ts: set<T>) {
      Complete?(ts) && /* Antisymmetric?(ts) && */ Transitive?(ts)
    }

    predicate Total?(ts: set<T>) { // TODO: Make this opaque?  Automated proofs can get very slow and costly
      Complete?(ts) && Antisymmetric?(ts) && Transitive?(ts)
    }

    predicate Sorted(sq: seq<T>) {
      forall i, j | 0 <= i < j < |sq| :: cmp(sq[i], sq[j]).Le?
    }

    lemma SortedConcat(sq0: seq<T>, sq1: seq<T>)
      requires Sorted(sq0)
      requires Sorted(sq1)
      requires forall i, j | 0 <= i < |sq0| && 0 <= j < |sq1| :: cmp(sq0[i], sq1[j]).Le?
      ensures Sorted(sq0 + sq1)
    {}

    // lemma SortedUnique(sq0: seq<T>, sq1: seq<T>)
    //   requires Sorted(sq0)
    //   requires Sorted(sq1)
    //   requires multiset(sq0) == multiset(sq1)
    //   requires Antisymmetric?(set x <- sq0)
    //   ensures sq0 == sq1
    // {
    //   calc { set x <- sq0; set x <- multiset(sq0); set x <- multiset(sq1); set x <- sq1; }
    // }

    predicate {:opaque} Striped(sq: seq<T>, pivot: T, lo: int, left: int, mid: int, right: int, hi: int)
      requires 0 <= lo <= left <= mid <= right <= hi <= |sq|
    {
      && (forall i | lo    <= i < left :: cmp(sq[i], pivot).Lt?)
      && (forall i | left  <= i < mid  :: cmp(sq[i], pivot).Eq?)
      && (forall i | right <= i < hi   :: cmp(sq[i], pivot).Gt?)
    }
  }
}

module Utils.Lib.Sort.DerivedComparison {
  import C = Comparison
  import Set

  datatype DerivedComparison<!T, !T'> = DerivedComparison(cmp: C.Comparison<T'>, fn: T -> T') {
    const Comparison := C.Comparison((t0, t1) => cmp.Compare(fn(t0), fn(t1)));

    lemma Valid(ts: set<T>)
      requires cmp.Valid?(Set.Map(ts, fn))
      ensures Comparison.Valid?(ts)
    {
      forall s0, s1 | s0 in ts && s1 in ts ensures Comparison.Complete??(s0, s1) {
        assert cmp.Complete??(fn(s0), fn(s1));
      }
      forall s0, s1, s2 | s0 in ts && s1 in ts && s2 in ts ensures Comparison.Transitive??(s0, s1, s2) {
        assert cmp.Transitive??(fn(s0), fn(s1), fn(s2));
      }
    }

    lemma Total(ts: set<T>)
      requires cmp.Total?(Set.Map(ts, fn))
      requires forall i, j | fn(i) == fn(j) :: i == j
      ensures Comparison.Total?(ts)
    {
      Valid(ts);
      forall s0, s1 | s0 in ts && s1 in ts ensures Comparison.Antisymmetric??(s0, s1) {
        calc ==> {
          Comparison.cmp(s0, s1).Eq?;
          cmp.cmp(fn(s0), fn(s1)).Eq?;
          { assert cmp.Antisymmetric??(fn(s0), fn(s1)); }
          fn(s0) == fn(s1);
          s0 == s1;
        }
      }
    }
  }
}

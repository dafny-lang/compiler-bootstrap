include "../AST/Syntax.dfy"
include "../Utils/Library.dfy"

module Bootstrap.Semantics.Values {
  import Utils.Lib.Math
  import opened Utils.Lib.Datatypes
  import AST.Syntax.Exprs
  import AST.Syntax.Types

  type Context = map<string, Value>

  datatype Value =
    | Unit
    | Bool(b: bool)
    | Char(c: char)
    | Int(i: int)
    | Real(r: real)
    | BigOrdinal(o: ORDINAL)
    | BitVector(width: nat, value: int)
    | Map(m: map<Value, Value>)
    | Multiset(ms: multiset<Value>)
    | Seq(sq: seq<Value>)
    | Set(st: set<Value>)
    | Closure(ctx: Context, vars: seq<string>, body: Exprs.T)
  {
    predicate method HasType(ty: Types.T)
      // Similarly to ``Equiv.EqValue``, this definition was initially written with a match
      // over the pair `(this, ty)`. We changed this: see the comment in ``Equiv.EqValue``
      // for detailed explanations.
    {
      this.WellFormed1() &&
      match this // FIXME tests on other side
        case Unit => ty.Unit?
        case Bool(b) => ty.Bool?
        case Char(c) => ty.Char?
        case Int(i) => ty.Int?
        case Real(r) => ty.Real?
        case BigOrdinal(o) => ty.BigOrdinal?
        case BitVector(width, value) =>
          && ty.BitVector?
          && width == ty.width
        case Map(m) =>
          && ty.Collection?
          && ty.finite
          && ty.kind.Map?
          && forall x | x in m :: x.HasType(ty.kind.keyType) && m[x].HasType(ty.eltType)
        case Multiset(ms) =>
          && ty.Collection?
          && ty.finite
          && ty.kind.Multiset?
          && forall x | x in ms :: x.HasType(ty.eltType)
        case Seq(sq) =>
          && ty.Collection?
          && ty.finite
          && ty.kind.Seq?
          && forall x | x in sq :: x.HasType(ty.eltType)
        case Set(st) =>
          && ty.Collection?
          && ty.finite
          && ty.kind.Set?
          && forall x | x in st :: x.HasType(ty.eltType)
        case Closure(ctx, vars, body) =>
          && ty.Function? // FIXME: Need a typing relation on terms, not just values
    }

    function method Children() : (cs: set<Value>)
      ensures forall c | c in cs :: c < this
    {
      match this
        case Unit => {}
        case Bool(b) => {}
        case Char(c) => {}
        case Int(i) => {}
        case Real(r) => {}
        case BigOrdinal(o) => {}
        case BitVector(width, value) => {}
        case Map(m) => m.Values
        case Multiset(ms) => set x | x in ms
        case Seq(sq) => set x | x in sq
        case Set(st) => st
        case Closure(ctx, vars_, body_) => ctx.Values
    }

    // This duplicates a bit ``Types.WellFormed()``.
    // More specifically, if we have ``value.HasType(t)``, then we can deduce from the type well-formedness
    // that we also have ``value.WellFormed()``.
    predicate method WellFormed1() {
      match this {
        case BitVector(width, val) =>
          0 <= value < Math.IntPow(2, width)
        case _ => true
      }
    }

    predicate method All(P: Value -> bool) {
      P(this) && forall c | c in this.Children() :: c.All(P)
    }

    lemma AllImpliesChildren(P: Value -> bool)
      requires All(P)
      ensures forall c | c in Children() :: c.All(P)
    {}

    function method Cast(ty: Types.T) : (v: Option<Value>)
      ensures v.Some? ==> HasType(ty)
    {
      if HasType(ty) then Some(this) else None
    }
  }

  type T = Value

  datatype TypedValue = Value(ty: Types.T, v: T) {
    predicate Wf() { v.HasType(ty) }
  }

  // FIXME how do we define the interpreter to support :| without committing to a single interpretation of :|?
  // NOTE: Maybe tag each syntactic :| with a distinct color and add the color somehow into the Dafny-side :| used to implement it.  Pro: it allows inlining.
}

module Bootstrap.Semantics { // DISCUSS: How do I add types to the parent module?  This works because I have only one
  type Value = Values.T
}

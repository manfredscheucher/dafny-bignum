/*******************************************************************************
 * dafny-bignum: verified arbitrary-precision arithmetic in pure Dafny.
 *
 * BigNat: unsigned arbitrary-precision natural numbers.
 *
 * Representation: little-endian sequence of 32-bit limbs (base 2^32). The first
 * limb is the least significant. A value is *normalized* when it has no leading
 * (most-significant) zero limbs, so every BigNat has a unique representation and
 * [] is the canonical zero.
 *
 * Every operation is specified against Value(), the mathematical nat the limbs
 * denote, and proved to agree with it. This mirrors the structure of Dafny's
 * Std.Arithmetic.LittleEndianNat (ToNatRight / SeqAdd / SeqSub), specialised to
 * concrete bv32 limbs so the code is runnable and translatable to any target
 * (no dependency on Dafny's own arbitrary-precision int in the representation).
 *******************************************************************************/

module BigNat {

  // Base of the positional system: 2^32. Limbs are bv32, so a single-limb
  // product fits in bv64 (2^32 * 2^32 = 2^64), which keeps the multiplication
  // proof free of any 128-bit reasoning.
  const BASE: nat := 0x1_0000_0000 // 2^32

  // A limb is a nat-backed digit in [0, BASE). Using a nat-backed newtype
  // (rather than bv32) keeps all carry/borrow/mul reasoning in plain nat
  // arithmetic, which the SMT solver handles cheaply; bit-vector<->nat casts
  // time out even in isolation. Translates to a native 32-bit integer.
  newtype limb = i: int | 0 <= i < 0x1_0000_0000

  // A limb interpreted as a nat, always in [0, BASE).
  function L(x: limb): nat { x as nat }

  lemma LimbBound(x: limb)
    ensures 0 <= L(x) < BASE
  {}

  //////////////////////////////////////////////////////////////////////////////
  // Value: limbs -> nat  (little-endian, least significant first)
  //////////////////////////////////////////////////////////////////////////////

  function Value(xs: seq<limb>): nat
  {
    if |xs| == 0 then 0
    else L(xs[0]) + BASE * Value(xs[1..])
  }

  // A sequence is normalized iff it has no leading zero limb.
  predicate Normalized(xs: seq<limb>)
  {
    |xs| == 0 || xs[|xs| - 1] != 0
  }

  lemma ValueBound(xs: seq<limb>)
    ensures Value(xs) < Pow2_32(|xs|)
  {
    if |xs| == 0 {
    } else {
      ValueBound(xs[1..]);
      calc {
        Value(xs);
        L(xs[0]) + BASE * Value(xs[1..]);
      <  { assert Value(xs[1..]) <= Pow2_32(|xs| - 1) - 1; }
        BASE + BASE * (Pow2_32(|xs| - 1) - 1);
        BASE * Pow2_32(|xs| - 1);
        Pow2_32(|xs|);
      }
    }
  }

  // BASE^n as a nat, defined recursively so proofs can unfold it.
  function Pow2_32(n: nat): nat
  {
    if n == 0 then 1 else BASE * Pow2_32(n - 1)
  }

  lemma Pow2_32Positive(n: nat)
    ensures Pow2_32(n) >= 1
  {
    if n == 0 {} else { Pow2_32Positive(n - 1); }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Normalization: drop leading zero limbs without changing Value.
  //////////////////////////////////////////////////////////////////////////////

  function Normalize(xs: seq<limb>): (ys: seq<limb>)
    ensures Normalized(ys)
    ensures Value(ys) == Value(xs)
  {
    if |xs| == 0 then []
    else if xs[|xs| - 1] == 0 then
      ValueDropLastZero(xs);
      Normalize(xs[..|xs| - 1])
    else
      xs
  }

  // Dropping a most-significant zero limb does not change Value.
  lemma ValueDropLastZero(xs: seq<limb>)
    requires |xs| > 0 && xs[|xs| - 1] == 0
    ensures Value(xs[..|xs| - 1]) == Value(xs)
  {
    ValueAppend(xs[..|xs| - 1], xs[|xs| - 1]);
    assert xs[..|xs| - 1] + [xs[|xs| - 1]] == xs;
  }

  // Appending one more-significant limb: Value(xs + [x]) == Value(xs) + BASE^|xs| * L(x).
  lemma ValueAppend(xs: seq<limb>, x: limb)
    ensures Value(xs + [x]) == Value(xs) + Pow2_32(|xs|) * L(x)
  {
    if |xs| == 0 {
      assert xs + [x] == [x];
    } else {
      ValueAppend(xs[1..], x);
      assert (xs + [x])[0] == xs[0];
      assert (xs + [x])[1..] == xs[1..] + [x];
      // The only nonlinear step: re-associate BASE * (Pow2_32(|xs|-1) * L(x)).
      MulAssoc(BASE, Pow2_32(|xs| - 1), L(x));
      assert BASE * (Pow2_32(|xs| - 1) * L(x)) == (BASE * Pow2_32(|xs| - 1)) * L(x);
      assert BASE * Pow2_32(|xs| - 1) == Pow2_32(|xs|);
      calc {
        Value(xs + [x]);
        L(xs[0]) + BASE * Value(xs[1..] + [x]);
        { assert Value(xs[1..] + [x]) == Value(xs[1..]) + Pow2_32(|xs| - 1) * L(x); }
        L(xs[0]) + BASE * (Value(xs[1..]) + Pow2_32(|xs| - 1) * L(x));
        { assert BASE * (Value(xs[1..]) + Pow2_32(|xs| - 1) * L(x))
                 == BASE * Value(xs[1..]) + BASE * (Pow2_32(|xs| - 1) * L(x)); }
        L(xs[0]) + BASE * Value(xs[1..]) + Pow2_32(|xs|) * L(x);
        Value(xs) + Pow2_32(|xs|) * L(x);
      }
    }
  }

  // Explicit associativity witness, so nonlinear reasoning is localised.
  lemma MulAssoc(a: nat, b: nat, c: nat)
    ensures a * (b * c) == (a * b) * c
  {}

  //////////////////////////////////////////////////////////////////////////////
  // Zero / one
  //////////////////////////////////////////////////////////////////////////////

  const Zero: seq<limb> := []
  const One: seq<limb> := [1]

  lemma ValueZero() ensures Value(Zero) == 0 {}
  lemma ValueOne() ensures Value(One) == 1 {}

  predicate IsZero(xs: seq<limb>) { xs == [] }

  lemma NormalizedZeroUnique(xs: seq<limb>)
    requires Normalized(xs) && Value(xs) == 0
    ensures xs == []
  {
    if |xs| != 0 {
      ValueBound(xs[1..]);
      // last limb is nonzero (normalized) yet Value==0 forces all limbs 0 — contradiction
      assert xs[|xs| - 1] != 0;
      ValueZeroAllZero(xs);
    }
  }

  lemma ValueZeroAllZero(xs: seq<limb>)
    requires Value(xs) == 0
    ensures forall i :: 0 <= i < |xs| ==> xs[i] == 0
  {
    if |xs| == 0 {
    } else {
      assert L(xs[0]) + BASE * Value(xs[1..]) == 0;
      assert L(xs[0]) == 0;
      assert xs[0] == 0;
      ValueZeroAllZero(xs[1..]);
    }
  }
}

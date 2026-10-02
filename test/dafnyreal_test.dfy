/*******************************************************************************
 * dafny-bignum: dafnyreal_test
 *
 * Verified regression checks for DafnyReal (the unreduced BigRational-style
 * real). Proving these lemmas IS the test. The important property is that the
 * representation stays UNREDUCED — 150/100 is NOT turned into 3/2 — while the
 * real value and the arithmetic are still correct.
 *******************************************************************************/

include "../src/BigNat.dfy"
include "../src/BigNatConv.dfy"
include "../src/BigInt.dfy"
include "../src/DafnyReal.dfy"

module DafnyRealTest {
  import opened BigNat
  import opened BigNatConv
  import BigInt
  import opened DafnyReal

  // Signed BigInt from a Dafny int.
  function OfInt(n: int): (r: BigInt.Int)
    ensures BigInt.Wf(r) && BigInt.IntValue(r) == n
  {
    if n >= 0 then BigInt.FromMagnitude(FromNat(n))
    else BigInt.Negate(BigInt.FromMagnitude(FromNat(-n)))
  }

  // num/den with den > 0, kept exactly as given (unreduced).
  function R(num: int, den: int): (x: DReal)
    requires den > 0
    ensures Wf(x)
    ensures RealValue(x) == num as real / den as real
  {
    Make(OfInt(num), OfInt(den))
  }

  // Precision is preserved: 150/100 is stored as 150/100, not reduced to 3/2.
  // Both denote 1.5, but the denominator (which drives print precision) is kept.
  lemma UnreducedKeepsDenominator()
    ensures BigInt.IntValue(R(150, 100).num) == 150
    ensures BigInt.IntValue(R(150, 100).den) == 100
    ensures RealValue(R(150, 100)) == 1.5
  {}

  // Same real value, different (unreduced) representations compare equal.
  lemma EqualValueDifferentRepr()
    ensures Compare(R(150, 100), R(3, 2)) == 0
    ensures Compare(R(1, 2), R(2, 4)) == 0
  {}

  // Arithmetic against the real value.
  lemma AddReals()
    ensures RealValue(Add(R(1, 2), R(1, 3))) == 1.0 / 2.0 + 1.0 / 3.0
    ensures RealValue(Add(R(3, 2), R(1, 2))) == 2.0
  {}

  lemma SubReals()
    ensures RealValue(Sub(R(3, 4), R(1, 4))) == 1.0 / 2.0
  {}

  lemma MulReals()
    ensures RealValue(Mul(R(2, 3), R(3, 4))) == (2.0 / 3.0) * (3.0 / 4.0)
  {}

  lemma DivReals()
    ensures RealValue(Div(R(1, 2), R(3, 4))) == (1.0 / 2.0) / (3.0 / 4.0)
  {}

  lemma NegReals()
    ensures RealValue(Neg(R(1, 4))) == -(1.0 / 4.0)
  {}

  // Ordering across signs and magnitudes.
  lemma CompareReals()
    ensures Compare(R(1, 3), R(1, 2)) < 0
    ensures Compare(R(-1, 2), R(1, 100)) < 0
    ensures Compare(R(5, 6), R(4, 6)) > 0
  {}
}

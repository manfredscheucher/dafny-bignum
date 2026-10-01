/*******************************************************************************
 * dafny-bignum: bigint_test
 *
 * Verified regression checks for signed BigInt. Proving these lemmas IS the
 * test: each asserts a concrete signed result against IntValue().
 *******************************************************************************/

include "../src/BigNat.dfy"
include "../src/BigNatConv.dfy"
include "../src/BigInt.dfy"

module BigIntTest {
  import opened BigNat
  import opened BigNatConv
  import opened BigInt

  // Build a signed Int from a Dafny int.
  function OfInt(n: int): (r: Int)
    ensures Wf(r) && IntValue(r) == n
  {
    if n >= 0 then FromMagnitude(FromNat(n))
    else Negate(FromMagnitude(FromNat(-n)))
  }

  lemma OfIntRoundTrip()
    ensures IntValue(OfInt(0)) == 0
    ensures IntValue(OfInt(5)) == 5
    ensures IntValue(OfInt(-5)) == -5
    ensures IntValue(OfInt(1000000000000000000000)) == 1000000000000000000000
    ensures IntValue(OfInt(-1000000000000000000000)) == -1000000000000000000000
  {}

  // Mixed-sign addition (the interesting case).
  lemma AddMixedSign()
    ensures IntValue(Add(OfInt(100), OfInt(-30))) == 70
    ensures IntValue(Add(OfInt(-100), OfInt(30))) == -70
    ensures IntValue(Add(OfInt(-100), OfInt(100))) == 0
    ensures IntValue(Add(OfInt(7), OfInt(-7))) == 0
  {}

  lemma SubExamples()
    ensures IntValue(Sub(OfInt(10), OfInt(25))) == -15
    ensures IntValue(Sub(OfInt(-10), OfInt(-25))) == 15
  {}

  // Sign of products.
  lemma MulSigns()
    ensures IntValue(Mul(OfInt(-6), OfInt(7))) == -42
    ensures IntValue(Mul(OfInt(-6), OfInt(-7))) == 42
    ensures IntValue(Mul(OfInt(123456789), OfInt(-1000000000))) == -123456789000000000
    ensures IntValue(Mul(OfInt(999), OfInt(0))) == 0
  {}

  // Comparison across signs.
  lemma CompareSigns()
    ensures Compare(OfInt(-1), OfInt(1)) < 0
    ensures Compare(OfInt(5), OfInt(5)) == 0
    ensures Compare(OfInt(-5), OfInt(-6)) > 0
    ensures Compare(OfInt(0), OfInt(-1)) > 0
  {}

  // Canonical zero: no "-0".
  lemma CanonicalZero()
    ensures OfInt(0) == BigInt.Zero
    ensures Negate(BigInt.Zero) == BigInt.Zero
    ensures !BigInt.Zero.negative && BigInt.Zero.mag == []
  {}
}

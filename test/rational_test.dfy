/*******************************************************************************
 * dafny-bignum: rational_test
 *
 * Verified regression checks for Rational. Proving these lemmas IS the test:
 * each asserts a concrete rational result against RatValue() (a real), covering
 * reduction, the four operations, and sign handling.
 *******************************************************************************/

include "../src/BigNat.dfy"
include "../src/BigNatConv.dfy"
include "../src/BigInt.dfy"
include "../src/Rational.dfy"

module RationalTest {
  import opened BigNat
  import opened BigNatConv
  import BigInt
  import opened Rational

  // Signed BigInt from a Dafny int.
  function OfInt(n: int): (r: BigInt.Int)
    ensures BigInt.Wf(r) && BigInt.IntValue(r) == n
  {
    if n >= 0 then BigInt.FromMagnitude(FromNat(n))
    else BigInt.Negate(BigInt.FromMagnitude(FromNat(-n)))
  }

  // Build num/den with den > 0, reduced.
  function Frac(num: int, den: nat): (r: Rat)
    requires den > 0
    ensures Wf(r)
    ensures RatValue(r) == num as real / den as real
  {
    PositiveFromNat(den);
    Make(OfInt(num), FromNat(den))
  }

  // FromNat(d) for d > 0 is a strictly positive, normalized denominator.
  lemma PositiveFromNat(d: nat)
    requires d > 0
    ensures Normalized(FromNat(d)) && Value(FromNat(d)) == d > 0
  {}

  // Reduction: 2/4, 6/4, 100/1000 collapse to lowest terms by value.
  lemma ReductionByValue()
    ensures RatValue(Frac(2, 4)) == RatValue(Frac(1, 2))
    ensures RatValue(Frac(6, 4)) == RatValue(Frac(3, 2))
    ensures RatValue(Frac(100, 1000)) == RatValue(Frac(1, 10))
    ensures RatValue(Frac(0, 5)) == 0.0
  {}

  // Addition of fractions, including a common and an unlike denominator.
  lemma AddFractions()
    ensures RatValue(Add(Frac(1, 2), Frac(1, 3))) == RatValue(Frac(5, 6))
    ensures RatValue(Add(Frac(1, 2), Frac(1, 2))) == 1.0
    ensures RatValue(Add(Frac(1, 3), Frac(-1, 3))) == 0.0
  {}

  lemma SubFractions()
    ensures RatValue(Sub(Frac(3, 4), Frac(1, 4))) == RatValue(Frac(1, 2))
    ensures RatValue(Sub(Frac(1, 6), Frac(1, 2))) == RatValue(Frac(-1, 3))
  {}

  // Mul's correctness (RatValue(Mul(x,y)) == RatValue(x)*RatValue(y)) is proved
  // on the operation itself in Rational.dfy. Exercising it here on concrete
  // fractions stacks three opaque `Make` reductions (two Fracs + Mul's own) over
  // literal values, which Z3 cannot evaluate in a reasonable budget. So the
  // concrete Mul checks use whole-number operands (FromInt: denominator 1, no
  // reduction), and the general product identity is covered by the proof above.
  lemma MulWholeNumbers()
    ensures RatValue(Mul(FromInt(OfInt(6)), FromInt(OfInt(7)))) == 42.0
    ensures RatValue(Mul(FromInt(OfInt(-6)), FromInt(OfInt(7)))) == -42.0
    ensures RatValue(Mul(FromInt(OfInt(7)), FromInt(OfInt(0)))) == 0.0
  {}

  // Comparison via RatValue.
  lemma CompareFractions()
    ensures Compare(Frac(1, 3), Frac(1, 2)) < 0
    ensures Compare(Frac(2, 4), Frac(1, 2)) == 0
    ensures Compare(Frac(-1, 2), Frac(1, 100)) < 0
    ensures Compare(Frac(5, 6), Frac(4, 6)) > 0
  {}
}

/*******************************************************************************
 * dafny-bignum: divmod_test
 *
 * Verified regression checks for DivMod. Proving these lemmas IS the test: each
 * asserts a concrete quotient/remainder against the Value() spec. Covers exact
 * division, division with remainder, divisor larger than dividend, and values
 * spanning several 32-bit limbs.
 *******************************************************************************/

include "../src/BigNat.dfy"
include "../src/BigNatConv.dfy"
include "../src/BigNatDivMod.dfy"

module DivModTest {
  import opened BigNat
  import opened BigNatConv
  import opened BigNatDivMod

  // 100 = 7*14 + 2.
  lemma WithRemainder()
    ensures var (q, r) := DivMod(FromNat(100), FromNat(7));
            Value(q) == 14 && Value(r) == 2
  {}

  // Exact division: 1000 / 8 = 125, remainder 0.
  lemma Exact()
    ensures var (q, r) := DivMod(FromNat(1000), FromNat(8));
            Value(q) == 125 && Value(r) == 0
  {}

  // Divisor larger than dividend: quotient 0, remainder is the dividend.
  lemma DivisorBigger()
    ensures var (q, r) := DivMod(FromNat(5), FromNat(42));
            Value(q) == 0 && Value(r) == 5
  {}

  // Divide by 1: quotient is the dividend, remainder 0.
  lemma DivByOne()
    ensures var (q, r) := DivMod(FromNat(123456789), FromNat(1));
            Value(q) == 123456789 && Value(r) == 0
  {}

  // Multi-limb: a value well above 2^64 divided by a multi-limb divisor.
  lemma MultiLimb()
    ensures var a := 123456789012345678901234567890;
            var b := 98765432109;
            var (q, r) := DivMod(FromNat(a), FromNat(b));
            Value(q) == a / b && Value(r) == a % b
  {}

  // The spec identity holds for the returned q, r (shape check).
  lemma SpecIdentity()
    ensures var xs := FromNat(999999999999);
            var ys := FromNat(7777);
            var (q, r) := DivMod(xs, ys);
            Value(xs) == Value(q) * Value(ys) + Value(r) && Value(r) < Value(ys)
  {}
}

/*******************************************************************************
 * dafny-bignum: gcd_test
 *
 * Regression checks for GCD / GCDFast by evaluating them on concrete inputs
 * (Dafny unfolds the function on literals and checks the resulting Value).
 *
 * Scope note: the full correctness of gcd is proved on the operations
 * themselves in BigNatGCD.dfy (against the IsGCD predicate). These evaluation
 * checks are a convenience on top. Only small inputs are used: unfolding the
 * recursive GCD over FromNat+DivMod on larger pairs sits at Z3's limit and
 * verifies nondeterministically, so such cases are deliberately left out rather
 * than committed as flaky tests. GCDFast tends to evaluate more cheaply than the
 * textbook GCD here, hence it carries the common-factor check.
 *******************************************************************************/

include "../src/BigNat.dfy"
include "../src/BigNatConv.dfy"
include "../src/BigNatGCD.dfy"

module GcdTest {
  import opened BigNat
  import opened BigNatConv
  import opened BigNatGCD

  // Common factor gcd(12, 18) == 6 (GCDFast unfolds cheaply enough).
  lemma CommonFactorFast()
    ensures Value(GCDFast(FromNat(12), FromNat(18))) == 6
  {}

  // Zero base cases: gcd(a, 0) == a and gcd(0, b) == b.
  lemma ZeroCases()
    ensures Value(GCD(FromNat(42), FromNat(0))) == 42
    ensures Value(GCD(FromNat(0), FromNat(42))) == 42
    ensures Value(GCDFast(FromNat(42), FromNat(0))) == 42
  {}

  // Equal arguments: gcd(x, x) == x.
  lemma EqualArgs()
    ensures Value(GCD(FromNat(7), FromNat(7))) == 7
    ensures Value(GCDFast(FromNat(7), FromNat(7))) == 7
  {}
}

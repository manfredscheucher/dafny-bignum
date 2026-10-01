/*******************************************************************************
 * dafny-bignum: nat_ops_test
 *
 * Verified regression checks for the unsigned operations. These are lemmas, so
 * `dafny verify` proving them IS the test — they assert concrete values of
 * Add / Sub / Mul / FromNat against their Value() spec. No runtime needed.
 *******************************************************************************/

include "../src/BigNat.dfy"
include "../src/BigNatConv.dfy"
include "../src/BigNatAddSub.dfy"
include "../src/BigNatMul.dfy"

module NatOpsTest {
  import opened BigNat
  import opened BigNatConv
  import opened BigNatAddSub
  import opened BigNatMul

  // FromNat round-trips through Value.
  lemma FromNatRoundTrip()
    ensures Value(FromNat(0)) == 0
    ensures Value(FromNat(1)) == 1
    ensures Value(FromNat(4294967296)) == 4294967296            // BASE
    ensures Value(FromNat(4294967297)) == 4294967297            // BASE + 1
    ensures Value(FromNat(123456789012345678901234567890)) == 123456789012345678901234567890
  {}

  // Zero is []; one is a single limb.
  lemma ZeroOneShape()
    ensures FromNat(0) == []
    ensures |FromNat(1)| == 1 && Value(FromNat(1)) == 1
  {}

  // Add agrees with + on a multi-limb example.
  lemma AddExample()
    ensures var a := FromNat(4294967295);                        // BASE - 1
            var b := FromNat(1);
            Value(Add(a, b)) == 4294967296                       // carries into a new limb
  {}

  // Sub agrees with - when the result spans fewer limbs.
  lemma SubExample()
    ensures var a := FromNat(4294967296);                        // BASE
            var b := FromNat(1);
            Value(Sub(a, b)) == 4294967295
  {}

  // Mul agrees with * on values that overflow a single limb.
  lemma MulExample()
    ensures var a := FromNat(4294967295);
            var b := FromNat(4294967295);
            Value(Mul(a, b)) == 4294967295 * 4294967295          // (2^32-1)^2
  {}

  // Multiplying by zero / one.
  lemma MulZeroOne()
    ensures var a := FromNat(12345678901234567890);
            Value(Mul(a, FromNat(0))) == 0
    ensures var a := FromNat(12345678901234567890);
            Value(Mul(a, FromNat(1))) == 12345678901234567890
  {}
}

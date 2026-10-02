include "/Users/manfred/github/dafny-bignum/src/BigNat.dfy"
include "/Users/manfred/github/dafny-bignum/src/BigNatConv.dfy"
include "/Users/manfred/github/dafny-bignum/src/BigNatGCD.dfy"
module T {
  import opened BigNat
  import opened BigNatConv
  import opened BigNatGCD
  // Direct evaluation: let Dafny unfold GCD on concrete literals.
  lemma EvalSmall()
    ensures Value(GCD(FromNat(12), FromNat(18))) == 6
  {}
}

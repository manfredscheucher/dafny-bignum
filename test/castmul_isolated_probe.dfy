module T {
  lemma CastMul(a: nat, b: nat)
    ensures (a * b) as real == (a as real) * (b as real)
  {}
}

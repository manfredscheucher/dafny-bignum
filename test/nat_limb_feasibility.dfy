// Does a plain nat-limb model avoid the bv blowup?
module T {
  const BASE: nat := 0x1_0000_0000
  newtype limb = i: int | 0 <= i < 0x1_0000_0000

  // nat-only carry decomposition — no bitvectors at all
  lemma NatSplit(x: nat, y: nat, c: nat)
    requires x < BASE && y < BASE && c <= 1
    ensures var s := x + y + c; s / BASE <= 1 && s % BASE == s - (s/BASE)*BASE
  {}

  lemma MulFits(x: nat, y: nat)
    requires x < BASE && y < BASE
    ensures x * y < BASE * BASE
  {
    // product of two things each < BASE
  }
}

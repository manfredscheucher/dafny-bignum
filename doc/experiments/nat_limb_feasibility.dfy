// Feasibility probe (kept for the record): does a plain nat-limb model avoid the
// bitvector blow-up that bv32 limbs caused? Yes — these facts verify instantly
// as pure nat arithmetic, which is why the whole library uses nat-backed limbs.
module T {
  const BASE: nat := 0x1_0000_0000
  newtype limb = i: int | 0 <= i < 0x1_0000_0000

  // nat-only carry decomposition — no bitvectors at all
  lemma NatSplit(x: nat, y: nat, c: nat)
    requires x < BASE && y < BASE && c <= 1
    ensures var s := x + y + c; s / BASE <= 1 && s % BASE == s - (s/BASE)*BASE
  {}

  // A single-limb product fits in a double-width window: x,y < BASE ⟹ x*y < BASE².
  lemma MulFits(x: nat, y: nat)
    requires x < BASE && y < BASE
    ensures x * y < BASE * BASE
  {
    // x*y <= x*(BASE-1) <= (BASE-1)*(BASE-1) < BASE*BASE
    MulMono(x, y, BASE - 1);       // y <= BASE-1 ==> x*y <= x*(BASE-1)
    MulMono(BASE - 1, x, BASE - 1); // x <= BASE-1 ==> x*(BASE-1) <= (BASE-1)*(BASE-1)
  }

  // b <= c ==> a*b <= a*c  (and symmetric use via commutativity)
  lemma MulMono(a: nat, b: nat, c: nat)
    requires b <= c
    ensures a * b <= a * c
  {}
}

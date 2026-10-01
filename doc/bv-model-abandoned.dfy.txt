/*******************************************************************************
 * dafny-bignum: BvLemmas
 *
 * The bit-vector <-> nat bridges used by the limb arithmetic, each proved in
 * isolation. These are the facts the SMT solver finds expensive in context
 * (mixing bv64 shift/mask with nat div/mod over a large sum), so they are
 * stated here as the smallest possible standalone lemmas and reused.
 *******************************************************************************/

module BvLemmas {

  const B32: nat := 0x1_0000_0000 // 2^32

  // Low 32 bits of a bv64 are its value mod 2^32.
  lemma LoIsMod(s: bv64)
    ensures ((s & 0xFFFF_FFFF) as nat) == (s as nat) % B32
  {}

  // High 32 bits (shift right by 32) of a bv64 are its value div 2^32.
  lemma HiIsDiv(s: bv64)
    ensures ((s >> 32) as nat) == (s as nat) / B32
  {}

  // Reassembly: a bv64 equals its high half times 2^32 plus its low half.
  lemma SplitAt32(s: bv64)
    ensures (s as nat) == ((s >> 32) as nat) * B32 + ((s & 0xFFFF_FFFF) as nat)
  {
    LoIsMod(s);
    HiIsDiv(s);
  }

  // A bv32 cast up to bv64 keeps its nat value.
  lemma Widen32(x: bv32)
    ensures (x as bv64) as nat == x as nat
  {}

  // Sum of two bv32 (widened) plus a carry bit does not overflow bv64 and its
  // nat value is the plain nat sum.
  lemma AddNoWrap(x: bv32, y: bv32, c: bv64)
    requires c as nat <= 1
    ensures ((x as bv64) + (y as bv64) + c) as nat
         == (x as nat) + (y as nat) + (c as nat)
  {}

  // Product of two bv32 (widened) does not overflow bv64: (2^32-1)^2 < 2^64.
  lemma MulNoWrap(x: bv32, y: bv32)
    ensures ((x as bv64) * (y as bv64)) as nat == (x as nat) * (y as nat)
  {}
}

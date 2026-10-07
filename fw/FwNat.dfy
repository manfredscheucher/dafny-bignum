/*******************************************************************************
 * dafny-bignum / fixed-width: FwNat
 *
 * Fixed-width BigNat. The HARD RULE that makes this actually replace Boost:
 * every EXECUTABLE value is a fixed-width newtype that carries a NativeType, so
 * the generated code uses native uint32/uint64 and never Dafny's unbounded int
 * (which the backends emit as BigNumber / Boost cpp_int / num / bignumber.js).
 *
 *   - limb:  newtype in [0, 2^32)  -> NativeType uint32
 *   - dword: newtype in [0, 2^64)  -> NativeType uint64 (carry/product window)
 *
 * `int`/`nat` appear ONLY in ghost specs and proofs (Value, lemmas), never in a
 * compiled expression. That separation is what keeps generated code Boost-free;
 * it is checked by translating to C++ and grepping for BigNumber (see fw/README).
 *
 * Representation: little-endian seq<limb>, least significant first, normalized
 * (no leading zero limb). Value() is the ghost nat it denotes.
 *******************************************************************************/

module FwNat {

  // 32-bit limb. Dafny assigns NativeType uint32 (smallest fitting type).
  newtype limb = x: int | 0 <= x < 0x1_0000_0000

  // 64-bit intermediate. NativeType uint64. Holds limb+limb+carry and limb*limb.
  newtype dword = x: int | 0 <= x < 0x1_0000_0000_0000_0000

  // Base 2^32, as a dword so limb arithmetic can widen into it.
  const BASE: dword := 0x1_0000_0000

  //////////////////////////////////////////////////////////////////////////////
  // Ghost value: limbs -> nat. GHOST, so it never enters compiled code.
  //////////////////////////////////////////////////////////////////////////////

  ghost function Value(xs: seq<limb>): nat
  {
    if |xs| == 0 then 0
    else (xs[0] as nat) + 0x1_0000_0000 * Value(xs[1..])
  }

  ghost predicate Normalized(xs: seq<limb>)
  {
    |xs| == 0 || xs[|xs| - 1] != 0
  }

  //////////////////////////////////////////////////////////////////////////////
  // AddCarry: add two limb sequences, fully fixed-width. No int in the body.
  //////////////////////////////////////////////////////////////////////////////

  // Add one limb column: a + b + carry-in, widened to a dword. Returns the low
  // limb and the carry-out limb (0 or 1). Proved against the integer identity.
  method AddColumn(a: limb, b: limb, cin: limb) returns (lo: limb, cout: limb)
    requires cin == 0 || cin == 1
    ensures cout == 0 || cout == 1
    ensures (a as nat) + (b as nat) + (cin as nat)
         == (cout as nat) * 0x1_0000_0000 + (lo as nat)
  {
    var s: dword := (a as dword) + (b as dword) + (cin as dword);
    lo := (s % BASE) as limb;
    cout := (s / BASE) as limb;
  }

  // Add two equal-length limb sequences with an incoming carry, returning the
  // result limbs (same length) and the final carry. Value-correct.
  method AddSeq(xs: seq<limb>, ys: seq<limb>, cin: limb)
      returns (zs: seq<limb>, cout: limb)
    requires |xs| == |ys|
    requires cin == 0 || cin == 1
    ensures |zs| == |xs|
    ensures cout == 0 || cout == 1
    ensures Value(xs) + Value(ys) + (cin as nat)
         == Value(zs) + (cout as nat) * Pow32(|xs|)
    decreases |xs|
  {
    if |xs| == 0 {
      return [], cin;
    }
    var lo, c1 := AddColumn(xs[0], ys[0], cin);
    var rest, c2 := AddSeq(xs[1..], ys[1..], c1);
    zs := [lo] + rest;
    cout := c2;
    AddSeqStep(xs, ys, cin, lo, c1, rest, c2, zs);
  }

  // 2^(32*n) as a ghost nat.
  ghost function Pow32(n: nat): nat
  {
    if n == 0 then 1 else 0x1_0000_0000 * Pow32(n - 1)
  }

  // Splice correctness for AddSeq's recursive step. All reasoning is ghost.
  lemma AddSeqStep(xs: seq<limb>, ys: seq<limb>, cin: limb,
                   lo: limb, c1: limb, rest: seq<limb>, c2: limb, zs: seq<limb>)
    requires |xs| == |ys| > 0
    requires (xs[0] as nat) + (ys[0] as nat) + (cin as nat)
          == (c1 as nat) * 0x1_0000_0000 + (lo as nat)
    requires Value(xs[1..]) + Value(ys[1..]) + (c1 as nat)
          == Value(rest) + (c2 as nat) * Pow32(|xs| - 1)
    requires zs == [lo] + rest
    ensures Value(xs) + Value(ys) + (cin as nat)
         == Value(zs) + (c2 as nat) * Pow32(|xs|)
  {
    assert zs[0] == lo && zs[1..] == rest;
    var B: nat := 0x1_0000_0000;
    // name every sub-value as a plain nat so the nonlinear steps are localised
    var vlo := lo as nat; var vc1 := c1 as nat; var vc2 := c2 as nat;
    var vxt := Value(xs[1..]); var vyt := Value(ys[1..]);
    var p := Pow32(|xs| - 1);
    // recursive hypothesis, rearranged
    assert Value(rest) == vxt + vyt + vc1 - vc2 * p;
    // column identity
    assert vlo + B * vc1 == (xs[0] as nat) + (ys[0] as nat) + (cin as nat);
    // Value unfolds on the head
    assert Value(xs) == (xs[0] as nat) + B * vxt;
    assert Value(ys) == (ys[0] as nat) + B * vyt;
    assert Value(zs) == vlo + B * Value(rest);
    // B * Pow32(|xs|-1) == Pow32(|xs|): directly from Pow32's definition.
    assert Pow32(|xs|) == 0x1_0000_0000 * Pow32(|xs| - 1);
    assert B * p == Pow32(|xs|);
    // distribute B over the rearranged Value(rest); each product named once
    DistribBig(B, vxt, vyt, vc1, vc2, p);
  }

  // B*(vxt+vyt+vc1 - vc2*p) == B*vxt + B*vyt + B*vc1 - (B*p)*vc2
  lemma DistribBig(B: nat, vxt: nat, vyt: nat, vc1: nat, vc2: nat, p: nat)
    ensures B * (vxt + vyt + vc1 - vc2 * p) == B*vxt + B*vyt + B*vc1 - (B*p)*vc2
  {}

  //////////////////////////////////////////////////////////////////////////////
  // Trivial, representation-independent nat algebra. Centralized here so the
  // other fw modules (all `import opened FwNat`) share one copy.
  //////////////////////////////////////////////////////////////////////////////

  lemma MulComm(a: nat, b: nat)
    ensures a * b == b * a
  {}

  lemma MulAssoc(a: nat, b: nat, c: nat)
    ensures a * (b * c) == (a * b) * c
  {}

  lemma Pow32Positive(n: nat)
    ensures Pow32(n) >= 1
  {
    if n == 0 {} else { Pow32Positive(n - 1); }
  }

  lemma Pow32Monotone(a: nat, b: nat)
    requires a <= b
    ensures Pow32(a) <= Pow32(b)
  {
    if a == b {} else { Pow32Monotone(a, b - 1); assert Pow32(b) == 0x1_0000_0000 * Pow32(b - 1); }
  }
}

/*******************************************************************************
 * dafny-bignum / fixed-width: FwSub
 *
 * Fixed-width subtraction, mirroring FwNat's AddColumn/AddSeq. Every executable
 * value is a fixed-width newtype (limb/dword); int/nat appear only in ghost
 * specs and lemmas, so the generated code stays Boost-free (native uint32/
 * uint64).
 *
 * SubColumn computes a - b - borrow in a dword window; SubSeq threads the borrow
 * through equal-length limb sequences. The spec is the borrow identity:
 *   Value(xs) + bout*2^(32*n) == Value(ys) + bin + Value(zs)
 *******************************************************************************/

include "FwNat.dfy"

module FwSub {
  import opened FwNat

  //////////////////////////////////////////////////////////////////////////////
  // SubColumn: a - b - bin, widened to a dword. Returns the difference limb and
  // the borrow-out (0 or 1). No int in the body.
  //////////////////////////////////////////////////////////////////////////////

  method SubColumn(a: limb, b: limb, bin: limb) returns (d: limb, bout: limb)
    requires bin == 0 || bin == 1
    ensures bout == 0 || bout == 1
    ensures (a as nat) + (bout as nat) * 0x1_0000_0000
         == (b as nat) + (bin as nat) + (d as nat)
  {
    var ad: dword := a as dword;
    var bd: dword := (b as dword) + (bin as dword);
    if ad >= bd {
      // no borrow: d = a - b - bin, bout = 0
      d := (ad - bd) as limb;
      bout := 0;
    } else {
      // borrow: d = BASE + a - b - bin, bout = 1
      d := (BASE + ad - bd) as limb;
      bout := 1;
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // SubSeq: subtract ys from xs (equal length) with incoming borrow. Returns the
  // difference limbs and the final borrow. Value-correct.
  //////////////////////////////////////////////////////////////////////////////

  method SubSeq(xs: seq<limb>, ys: seq<limb>, bin: limb)
      returns (zs: seq<limb>, bout: limb)
    requires |xs| == |ys|
    requires bin == 0 || bin == 1
    ensures |zs| == |xs|
    ensures bout == 0 || bout == 1
    ensures Value(xs) + (bout as nat) * Pow32(|xs|)
         == Value(ys) + (bin as nat) + Value(zs)
    decreases |xs|
  {
    if |xs| == 0 {
      return [], bin;
    }
    var d, b1 := SubColumn(xs[0], ys[0], bin);
    var rest, b2 := SubSeq(xs[1..], ys[1..], b1);
    zs := [d] + rest;
    bout := b2;
    SubSeqStep(xs, ys, bin, d, b1, rest, b2, zs);
  }

  // Splice correctness for SubSeq's recursive step. All reasoning is ghost.
  lemma SubSeqStep(xs: seq<limb>, ys: seq<limb>, bin: limb,
                   d: limb, b1: limb, rest: seq<limb>, b2: limb, zs: seq<limb>)
    requires |xs| == |ys| > 0
    requires (xs[0] as nat) + (b1 as nat) * 0x1_0000_0000
          == (ys[0] as nat) + (bin as nat) + (d as nat)
    requires Value(xs[1..]) + (b2 as nat) * Pow32(|xs| - 1)
          == Value(ys[1..]) + (b1 as nat) + Value(rest)
    requires zs == [d] + rest
    ensures Value(xs) + (b2 as nat) * Pow32(|xs|)
         == Value(ys) + (bin as nat) + Value(zs)
  {
    assert zs[0] == d && zs[1..] == rest;
    var B: nat := 0x1_0000_0000;
    // name every sub-value as a plain nat so the nonlinear steps are localised
    var vd := d as nat; var vb1 := b1 as nat; var vb2 := b2 as nat;
    var vxt := Value(xs[1..]); var vyt := Value(ys[1..]); var vr := Value(rest);
    var p := Pow32(|xs| - 1);
    // column identity: xs[0] + b1*B == ys[0] + bin + d
    assert (xs[0] as nat) + vb1 * B == (ys[0] as nat) + (bin as nat) + vd;
    // recursive hypothesis: vxt + b2*p == vyt + b1 + vr
    assert vxt + vb2 * p == vyt + vb1 + vr;
    // Value unfolds on the head
    assert Value(xs) == (xs[0] as nat) + B * vxt;
    assert Value(ys) == (ys[0] as nat) + B * vyt;
    assert Value(zs) == vd + B * vr;
    // B * Pow32(|xs|-1) == Pow32(|xs|): directly from Pow32's definition.
    assert Pow32(|xs|) == 0x1_0000_0000 * Pow32(|xs| - 1);
    assert B * p == Pow32(|xs|);
    // the one nonlinear distribution step, given explicitly
    DistribSub(B, vxt, vyt, vr, vb1, vb2, p);
  }

  // B*(vxt) with the recursion vxt = vyt + vb1 + vr - vb2*p distributed:
  //   B*vxt == B*vyt + B*vb1 + B*vr - (B*p)*vb2
  lemma DistribSub(B: nat, vxt: nat, vyt: nat, vr: nat, vb1: nat, vb2: nat, p: nat)
    ensures B * (vyt + vb1 + vr - vb2 * p) == B*vyt + B*vb1 + B*vr - (B*p)*vb2
  {}
}

/*******************************************************************************
 * dafny-bignum / fixed-width: FwCompare
 *
 * Fixed-width comparison of normalized limb sequences. Returns -1/0/1 for
 * Value(xs) </==/> Value(ys). Executable values are limbs only (the result is a
 * plain comparison int, which is fine — it is a bounded {-1,0,1} result, not an
 * unbounded counter; still, we return it as the small ints -1/0/1 which the
 * backend emits natively, and no nat/int flows through the recursion).
 *******************************************************************************/

include "FwNat.dfy"

module FwCompare {
  import opened FwNat

  // Result type: a native 8-bit value in {-1,0,1}. A plain `int` return would
  // compile to an unbounded integer (Boost) — this newtype gets a NativeType.
  newtype cmp = x: int | -1 <= x <= 1

  // Compare two NORMALIZED sequences. Length decides first (normalized: longer is
  // strictly larger); equal lengths compare limb-wise. Fully fixed-width: the
  // recursion is LSB-first over xs[1..] (no `|xs|-1` index in compiled code), and
  // the result is the native `cmp`, so nothing unbounded is generated.
  method Compare(xs: seq<limb>, ys: seq<limb>) returns (c: cmp)
    requires Normalized(xs) && Normalized(ys)
    ensures c == 0 <==> Value(xs) == Value(ys)
    ensures c < 0 <==> Value(xs) < Value(ys)
    ensures c > 0 <==> Value(xs) > Value(ys)
  {
    if |xs| != |ys| {
      CompareByLength(xs, ys);
      return if |xs| < |ys| then -1 else 1;
    }
    c := CompareEqualLen(xs, ys);
  }

  // Equal-length comparison, LSB-first over xs[1..]. The higher-order limbs
  // dominate: if the tails differ, their order decides; otherwise the head
  // limbs decide. No numeric index is bound in compiled code.
  method CompareEqualLen(xs: seq<limb>, ys: seq<limb>) returns (c: cmp)
    requires |xs| == |ys|
    ensures c == 0 <==> Value(xs) == Value(ys)
    ensures c < 0 <==> Value(xs) < Value(ys)
    ensures c > 0 <==> Value(xs) > Value(ys)
    decreases |xs|
  {
    if |xs| == 0 {
      return 0;
    }
    var ctail := CompareEqualLen(xs[1..], ys[1..]);
    if ctail != 0 {
      LsbTailDecides(xs, ys, ctail);
      return ctail;
    }
    // tails equal: head limbs decide
    LsbHeadDecides(xs, ys);
    if xs[0] < ys[0] { c := -1; }
    else if xs[0] > ys[0] { c := 1; }
    else { c := 0; }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Ghost lemmas tying the structural comparison to Value().
  //////////////////////////////////////////////////////////////////////////////

  // Value bound: a length-n sequence is < 2^(32n).
  lemma ValueBound(xs: seq<limb>)
    ensures Value(xs) < Pow32(|xs|)
  {
    if |xs| == 0 {
    } else {
      ValueBound(xs[1..]);
      var B := 0x1_0000_0000;
      assert Value(xs) == (xs[0] as nat) + B * Value(xs[1..]);
      assert Value(xs[1..]) <= Pow32(|xs| - 1) - 1;
      assert B * Value(xs[1..]) <= B * (Pow32(|xs| - 1) - 1);
      assert Pow32(|xs|) == B * Pow32(|xs| - 1);
    }
  }

  // Normalized + longer ==> strictly larger.
  lemma CompareByLength(xs: seq<limb>, ys: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    requires |xs| != |ys|
    ensures |xs| < |ys| ==> Value(xs) < Value(ys)
    ensures |xs| > |ys| ==> Value(xs) > Value(ys)
  {
    if |xs| < |ys| {
      ShorterIsSmaller(xs, ys);
    } else {
      ShorterIsSmaller(ys, xs);
    }
  }

  // If |a| < |b| and b is normalized, Value(a) < Value(b).
  lemma ShorterIsSmaller(a: seq<limb>, b: seq<limb>)
    requires Normalized(a) && Normalized(b)
    requires |a| < |b|
    ensures Value(a) < Value(b)
  {
    ValueBound(a);                       // Value(a) < Pow32(|a|) <= Pow32(|b|-1)
    Pow32Monotone(|a|, |b| - 1);
    // b normalized, |b|>0: Value(b) >= Pow32(|b|-1) (top limb >= 1)
    TopLimbLowerBound(b);
  }

  // A normalized nonempty sequence has Value >= Pow32(len-1).
  lemma TopLimbLowerBound(b: seq<limb>)
    requires Normalized(b) && |b| > 0
    ensures Value(b) >= Pow32(|b| - 1)
  {
    var n := |b| - 1;
    var B := 0x1_0000_0000;
    if n == 0 {
      assert Value(b) == (b[0] as nat);
      assert b[0] != 0;
    } else {
      // Value(b) = b[0] + B*Value(b[1..]); b[1..] is normalized nonempty.
      assert b[1..][|b[1..]| - 1] == b[n];
      TopLimbLowerBound(b[1..]);
      assert Value(b[1..]) >= Pow32(n - 1);
      assert Value(b) >= B * Value(b[1..]);
      assert B * Pow32(n - 1) == Pow32(n);
      assert B * Value(b[1..]) >= B * Pow32(n - 1);
    }
  }

  lemma Pow32Monotone(a: nat, b: nat)
    requires a <= b
    ensures Pow32(a) <= Pow32(b)
  {
    if a == b {} else { Pow32Monotone(a, b - 1); assert Pow32(b) == 0x1_0000_0000 * Pow32(b - 1); }
  }

  // LSB-first: if the tails (xs[1..] vs ys[1..]) differ, they decide the order,
  // because the tail is scaled by B and the head limbs are < B so cannot bridge
  // a tail gap of at least one.
  lemma LsbTailDecides(xs: seq<limb>, ys: seq<limb>, ctail: cmp)
    requires |xs| == |ys| > 0
    requires ctail != 0
    requires ctail < 0 <==> Value(xs[1..]) < Value(ys[1..])
    requires ctail > 0 <==> Value(xs[1..]) > Value(ys[1..])
    ensures ctail < 0 <==> Value(xs) < Value(ys)
    ensures ctail > 0 <==> Value(xs) > Value(ys)
  {
    var B := 0x1_0000_0000;
    var xh := xs[0] as nat; var yh := ys[0] as nat;
    var xt := Value(xs[1..]); var yt := Value(ys[1..]);
    assert Value(xs) == xh + B * xt;
    assert Value(ys) == yh + B * yt;
    assert xh < B && yh < B;
    // if xt < yt then xt+1 <= yt, so B*yt - B*xt >= B > xh, hence Value(xs)<Value(ys)
    if xt < yt { TailGap(B, xt, yt); }
    if xt > yt { TailGap(B, yt, xt); }
  }

  // a < b (nats) ==> B*b >= B*a + B.  Isolated nonlinear step.
  lemma TailGap(B: nat, a: nat, b: nat)
    requires a < b
    ensures B * b >= B * a + B
  {
    assert b >= a + 1;
    assert B * b >= B * (a + 1);
  }

  // LSB-first: equal tails ==> the head limbs decide.
  lemma LsbHeadDecides(xs: seq<limb>, ys: seq<limb>)
    requires |xs| == |ys| > 0
    requires Value(xs[1..]) == Value(ys[1..])
    ensures (xs[0] as nat) < (ys[0] as nat) ==> Value(xs) < Value(ys)
    ensures (xs[0] as nat) > (ys[0] as nat) ==> Value(xs) > Value(ys)
    ensures (xs[0] as nat) == (ys[0] as nat) ==> Value(xs) == Value(ys)
  {
    assert Value(xs) == (xs[0] as nat) + 0x1_0000_0000 * Value(xs[1..]);
    assert Value(ys) == (ys[0] as nat) + 0x1_0000_0000 * Value(ys[1..]);
  }
}

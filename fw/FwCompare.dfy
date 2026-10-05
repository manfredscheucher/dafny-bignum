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

  // Compare two NORMALIZED sequences. For normalized numbers the longer one is
  // strictly larger, so length decides first; equal lengths compare MSB-first.
  method Compare(xs: seq<limb>, ys: seq<limb>) returns (c: int)
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

  // Equal-length comparison, MSB first. Recurses on the sequences (drop the last
  // limb), never on a numeric index, so nothing unbounded is compiled.
  method CompareEqualLen(xs: seq<limb>, ys: seq<limb>) returns (c: int)
    requires |xs| == |ys|
    ensures c == 0 <==> Value(xs) == Value(ys)
    ensures c < 0 <==> Value(xs) < Value(ys)
    ensures c > 0 <==> Value(xs) > Value(ys)
    decreases |xs|
  {
    if |xs| == 0 {
      return 0;
    }
    var n := |xs| - 1;
    if xs[n] != ys[n] {
      MswDecides(xs, ys);
      return if xs[n] < ys[n] then -1 else 1;
    }
    var c0 := CompareEqualLen(xs[..n], ys[..n]);
    EqualLenStep(xs, ys, c0);
    c := c0;
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

  // If the most significant limb differs, it decides the order.
  lemma MswDecides(xs: seq<limb>, ys: seq<limb>)
    requires |xs| == |ys| > 0
    requires xs[|xs| - 1] != ys[|ys| - 1]
    ensures xs[|xs| - 1] < ys[|ys| - 1] ==> Value(xs) < Value(ys)
    ensures xs[|xs| - 1] > ys[|ys| - 1] ==> Value(xs) > Value(ys)
  {
    var n := |xs| - 1;
    PrefixPlusTop(xs);
    PrefixPlusTop(ys);
    ValueBound(xs[..n]);
    ValueBound(ys[..n]);
    // Value = Value(prefix) + Pow32(n)*top, prefix < Pow32(n), so top decides.
  }

  // Value(s) == Value(s[..n]) + Pow32(n) * s[n], n == |s|-1.
  lemma PrefixPlusTop(s: seq<limb>)
    requires |s| > 0
    ensures Value(s) == Value(s[..|s| - 1]) + Pow32(|s| - 1) * (s[|s| - 1] as nat)
  {
    var n := |s| - 1;
    var B := 0x1_0000_0000;
    if n == 0 {
      assert s[..0] == [];
      assert Value(s) == (s[0] as nat);
    } else {
      PrefixPlusTop(s[1..]);
      assert s[1..][..n - 1] == s[1..n];
      assert s[..n][1..] == s[1..n];
      assert s[1..][|s[1..]| - 1] == s[n];
      // bind the sub-values as plain nats; do the nonlinear algebra in one lemma
      var vt := Value(s[1..n]);
      var top := s[n] as nat;
      var p := Pow32(n - 1);
      assert Value(s[1..]) == vt + p * top;            // recursive hypothesis
      assert Pow32(n) == B * p;                         // Pow32 definition
      assert Value(s[..n]) == (s[0] as nat) + B * vt;   // head unfold of prefix
      PrefixTopAlgebra(B, s[0] as nat, vt, p, top);
    }
  }

  // (h + B*(vt + p*top)) == (h + B*vt) + (B*p)*top. One isolated nonlinear step.
  lemma PrefixTopAlgebra(B: nat, h: nat, vt: nat, p: nat, top: nat)
    ensures h + B * (vt + p * top) == (h + B * vt) + (B * p) * top
  {}

  // Equal top limb: the order is decided by the prefixes.
  lemma EqualLenStep(xs: seq<limb>, ys: seq<limb>, c0: int)
    requires |xs| == |ys| > 0
    requires xs[|xs| - 1] == ys[|ys| - 1]
    requires c0 == 0 <==> Value(xs[..|xs| - 1]) == Value(ys[..|ys| - 1])
    requires c0 < 0 <==> Value(xs[..|xs| - 1]) < Value(ys[..|ys| - 1])
    requires c0 > 0 <==> Value(xs[..|xs| - 1]) > Value(ys[..|ys| - 1])
    ensures c0 == 0 <==> Value(xs) == Value(ys)
    ensures c0 < 0 <==> Value(xs) < Value(ys)
    ensures c0 > 0 <==> Value(xs) > Value(ys)
  {
    PrefixPlusTop(xs);
    PrefixPlusTop(ys);
    // same top limb and same Pow32 factor, so the prefixes decide identically.
  }
}

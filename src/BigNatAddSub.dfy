/*******************************************************************************
 * dafny-bignum: BigNatAddSub
 *
 * Verified comparison, addition, and subtraction on little-endian nat-backed
 * limb natural numbers, specified against BigNat.Value.
 *
 * Design note: unlike Std.Arithmetic.LittleEndianNat (which works over equal
 * length sequences via the MSB / DropLast recursion), these operations recurse
 * on the LEAST significant limb (the head, xs[0]), which is exactly how
 * BigNat.Value is defined:  Value(xs) == L(xs[0]) + BASE * Value(xs[1..]).
 * That keeps the carry/borrow induction aligned with the spec and lets Add/Sub
 * handle sequences of different lengths directly, without padding.
 *******************************************************************************/

include "BigNat.dfy"

module BigNatAddSub {
  import opened BigNat

  //////////////////////////////////////////////////////////////////////////////
  // Comparison (expects normalized inputs)
  //////////////////////////////////////////////////////////////////////////////

  // Compare two normalized limb sequences: -1 if Value(xs) < Value(ys),
  // 0 if equal, 1 if greater.
  function Compare(xs: seq<limb>, ys: seq<limb>): (r: int)
    requires Normalized(xs) && Normalized(ys)
    ensures r == 0 <==> Value(xs) == Value(ys)
    ensures r < 0 <==> Value(xs) < Value(ys)
    ensures r > 0 <==> Value(xs) > Value(ys)
  {
    if |xs| != |ys| then
      // Normalized numbers: the longer one is strictly larger.
      CompareByLength(xs, ys);
      if |xs| < |ys| then -1 else 1
    else
      CompareEqualLen(xs, ys)
  }

  // For normalized sequences of different lengths, the longer denotes the
  // larger value.
  lemma CompareByLength(xs: seq<limb>, ys: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    requires |xs| != |ys|
    ensures |xs| < |ys| ==> Value(xs) < Value(ys)
    ensures |xs| > |ys| ==> Value(xs) > Value(ys)
  {
    if |xs| < |ys| {
      NormalizedLowerBound(ys);
      ValueBound(xs);
      // Value(xs) < BASE^|xs| <= BASE^(|ys|-1) <= Value(ys)
      Pow2_32Monotone(|xs|, |ys| - 1);
    } else {
      NormalizedLowerBound(xs);
      ValueBound(ys);
      Pow2_32Monotone(|ys|, |xs| - 1);
    }
  }

  // A normalized sequence of length n >= 1 has Value >= BASE^(n-1) (its top
  // limb is nonzero).
  lemma NormalizedLowerBound(xs: seq<limb>)
    requires Normalized(xs) && |xs| > 0
    ensures Value(xs) >= Pow2_32(|xs| - 1)
  {
    // Value(xs) == Value(xs[..|xs|-1]) + BASE^(|xs|-1) * L(last), last >= 1.
    ValueAppend(xs[..|xs| - 1], xs[|xs| - 1]);
    assert xs[..|xs| - 1] + [xs[|xs| - 1]] == xs;
    assert L(xs[|xs| - 1]) >= 1;
    Pow2_32Positive(|xs| - 1);
    MulLowerBound(Pow2_32(|xs| - 1), L(xs[|xs| - 1]));
  }

  // If a >= 0 and b >= 1 then a * b >= a.
  lemma MulLowerBound(a: nat, b: nat)
    requires b >= 1
    ensures a * b >= a
  {
    MulMonoRight(a, 1, b);
  }

  // Monotonicity of Pow2_32 in the exponent.
  lemma Pow2_32Monotone(a: nat, b: nat)
    requires a <= b
    ensures Pow2_32(a) <= Pow2_32(b)
  {
    if a == b {
    } else {
      Pow2_32Monotone(a, b - 1);
      Pow2_32Positive(b - 1);
      // Pow2_32(b) == BASE * Pow2_32(b-1) >= Pow2_32(b-1) >= Pow2_32(a)
      MulLowerBoundLeft(Pow2_32(b - 1), BASE);
    }
  }

  // If a >= 0 and m >= 1 then m * a >= a.
  lemma MulLowerBoundLeft(a: nat, m: nat)
    requires m >= 1
    ensures m * a >= a
  {
    MulMonoLeft(1, m, a);
  }

  // Compare two equal-length sequences from the most significant limb down.
  function CompareEqualLen(xs: seq<limb>, ys: seq<limb>): (r: int)
    requires |xs| == |ys|
    ensures r == 0 <==> Value(xs) == Value(ys)
    ensures r < 0 <==> Value(xs) < Value(ys)
    ensures r > 0 <==> Value(xs) > Value(ys)
    decreases |xs|
  {
    if |xs| == 0 then 0
    else
      var n := |xs| - 1;
      if xs[n] != ys[n] then
        MswDecides(xs, ys);
        if xs[n] < ys[n] then -1 else 1
      else
        // Top limbs equal: compare the prefixes, top limb contributes equally.
        PrefixDecides(xs, ys);
        CompareEqualLen(xs[..n], ys[..n])
  }

  // If the most significant limbs differ, they decide the ordering regardless
  // of the lower limbs.
  lemma MswDecides(xs: seq<limb>, ys: seq<limb>)
    requires |xs| == |ys| > 0
    requires xs[|xs| - 1] != ys[|ys| - 1]
    ensures xs[|xs| - 1] < ys[|ys| - 1] ==> Value(xs) < Value(ys)
    ensures xs[|xs| - 1] > ys[|ys| - 1] ==> Value(xs) > Value(ys)
  {
    var n := |xs| - 1;
    ValueAppend(xs[..n], xs[n]);
    ValueAppend(ys[..n], ys[n]);
    assert xs[..n] + [xs[n]] == xs;
    assert ys[..n] + [ys[n]] == ys;
    var pow := Pow2_32(n);
    Pow2_32Positive(n);
    // Value(xs) = Value(xs[..n]) + pow * L(xs[n]); same shape for ys.
    ValueBound(xs[..n]);
    ValueBound(ys[..n]);
    if xs[n] < ys[n] {
      // Value(xs) < pow*(L(xs[n])+1) <= pow*L(ys[n]) <= Value(ys)
      MswGap(Value(xs[..n]), L(xs[n]), Value(ys[..n]), L(ys[n]), pow);
    } else {
      MswGap(Value(ys[..n]), L(ys[n]), Value(xs[..n]), L(xs[n]), pow);
    }
  }

  // Core arithmetic gap lemma for MswDecides: if lo < pow and dl < dh then
  // lo + pow*dl < ho + pow*dh (with ho >= 0).
  lemma MswGap(lo: nat, dl: nat, ho: nat, dh: nat, pow: nat)
    requires lo < pow
    requires dl < dh
    ensures lo + pow * dl < ho + pow * dh
  {
    // pow*dh - pow*dl = pow*(dh-dl) >= pow > lo
    MulMonoRight(pow, dl + 1, dh);
    // pow*(dl+1) <= pow*dh
    assert pow * (dl + 1) == pow * dl + pow by { MulDistrib(pow, dl, 1); }
    // lo + pow*dl < pow + pow*dl == pow*(dl+1) <= pow*dh <= ho + pow*dh
  }

  // If the top limbs are equal, comparing prefixes decides the full order.
  lemma PrefixDecides(xs: seq<limb>, ys: seq<limb>)
    requires |xs| == |ys| > 0
    requires xs[|xs| - 1] == ys[|ys| - 1]
    ensures Value(xs) < Value(ys) <==> Value(xs[..|xs| - 1]) < Value(ys[..|ys| - 1])
    ensures Value(xs) == Value(ys) <==> Value(xs[..|xs| - 1]) == Value(ys[..|ys| - 1])
    ensures Value(xs) > Value(ys) <==> Value(xs[..|xs| - 1]) > Value(ys[..|ys| - 1])
  {
    var n := |xs| - 1;
    ValueAppend(xs[..n], xs[n]);
    ValueAppend(ys[..n], ys[n]);
    assert xs[..n] + [xs[n]] == xs;
    assert ys[..n] + [ys[n]] == ys;
    // Value(xs) = Value(xs[..n]) + pow*L(xs[n]); the pow*L term is identical.
  }

  //////////////////////////////////////////////////////////////////////////////
  // Addition (LSB-first carry), handles unequal lengths, result normalized
  //////////////////////////////////////////////////////////////////////////////

  // Add with an incoming carry (0 or 1), returning limbs whose Value is exactly
  // Value(xs) + Value(ys) + cin.  Not necessarily normalized.
  function AddCarry(xs: seq<limb>, ys: seq<limb>, cin: limb): (zs: seq<limb>)
    requires cin == 0 || cin == 1
    ensures Value(zs) == Value(xs) + Value(ys) + L(cin)
    decreases |xs| + |ys|
  {
    if |xs| == 0 && |ys| == 0 then
      if cin == 0 then [] else [cin]
    else
      // head limbs (0 if the sequence is empty) plus carry, in plain nat
      var xh: nat := if |xs| == 0 then 0 else L(xs[0]);
      var yh: nat := if |ys| == 0 then 0 else L(ys[0]);
      var s: nat := xh + yh + L(cin);
      var lo: limb := (s % BASE) as limb;
      var carry: limb := (s / BASE) as limb;
      HeadSumDecompose(xs, ys, cin, s, lo, carry);
      var xt := if |xs| == 0 then [] else xs[1..];
      var yt := if |ys| == 0 then [] else ys[1..];
      var rest := AddCarry(xt, yt, carry);
      AddCarryStep(xs, ys, cin, lo, carry, rest);
      [lo] + rest
  }

  // For xh,yh < 2^32 and cin in {0,1}, s = xh+yh+cin satisfies s < 2*BASE, so the
  // Euclidean split s == carry*BASE + lo has carry in {0,1} and lo < BASE.
  lemma HeadSumDecompose(xs: seq<limb>, ys: seq<limb>, cin: limb,
                         s: nat, lo: limb, carry: limb)
    requires cin == 0 || cin == 1
    requires s == (if |xs| == 0 then 0 else L(xs[0]))
               + (if |ys| == 0 then 0 else L(ys[0]))
               + L(cin)
    requires lo == (s % BASE) as limb
    requires carry == (s / BASE) as limb
    ensures carry == 0 || carry == 1
    ensures (if |xs| == 0 then 0 else L(xs[0]))
          + (if |ys| == 0 then 0 else L(ys[0]))
          + L(cin)
          == L(carry) * BASE + L(lo)
  {
    // s < BASE + BASE + 1 <= 2*BASE, hence s / BASE in {0, 1}.
    assert s < 2 * BASE;
    assert L(carry) == s / BASE;
    assert L(lo) == s % BASE;
    // Fundamental division: s == (s/BASE)*BASE + s%BASE.
  }

  // Splice step: [lo] + rest has the intended Value given the decomposition.
  lemma AddCarryStep(xs: seq<limb>, ys: seq<limb>, cin: limb,
                     lo: limb, carry: limb, rest: seq<limb>)
    requires cin == 0 || cin == 1
    requires carry == 0 || carry == 1
    requires (if |xs| == 0 then 0 else L(xs[0]))
           + (if |ys| == 0 then 0 else L(ys[0]))
           + L(cin)
           == L(carry) * BASE + L(lo)
    requires var xt := if |xs| == 0 then [] else xs[1..];
             var yt := if |ys| == 0 then [] else ys[1..];
             Value(rest) == Value(xt) + Value(yt) + L(carry)
    ensures Value([lo] + rest) == Value(xs) + Value(ys) + L(cin)
  {
    var xt := if |xs| == 0 then [] else xs[1..];
    var yt := if |ys| == 0 then [] else ys[1..];
    assert ([lo] + rest)[0] == lo;
    assert ([lo] + rest)[1..] == rest;
    // Value([lo]+rest) = L(lo) + BASE*Value(rest)
    //                  = L(lo) + BASE*(Value(xt)+Value(yt)+L(carry))
    calc {
      Value([lo] + rest);
      L(lo) + BASE * Value(rest);
      L(lo) + BASE * (Value(xt) + Value(yt) + L(carry));
      { MulDistrib3(BASE, Value(xt), Value(yt), L(carry)); }
      L(lo) + BASE * Value(xt) + BASE * Value(yt) + BASE * L(carry);
      { assert L(carry) * BASE == BASE * L(carry); }
      (L(lo) + L(carry) * BASE) + BASE * Value(xt) + BASE * Value(yt);
      (if |xs| == 0 then 0 else L(xs[0])) + (if |ys| == 0 then 0 else L(ys[0])) + L(cin)
        + BASE * Value(xt) + BASE * Value(yt);
      { HeadTailValue(xs); HeadTailValue(ys); }
      Value(xs) + Value(ys) + L(cin);
    }
  }

  // Value(xs) == (head) + BASE * Value(tail), respecting the empty case.
  lemma HeadTailValue(xs: seq<limb>)
    ensures Value(xs) == (if |xs| == 0 then 0 else L(xs[0]))
                       + BASE * Value(if |xs| == 0 then [] else xs[1..])
  {
    if |xs| == 0 {
    } else {
      // directly from the definition of Value
    }
  }

  // Public addition: sum of two (normalized) BigNats, normalized result.
  function Add(xs: seq<limb>, ys: seq<limb>): (zs: seq<limb>)
    ensures Value(zs) == Value(xs) + Value(ys)
    ensures Normalized(zs)
  {
    var raw := AddCarry(xs, ys, 0);
    Normalize(raw)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Subtraction (LSB-first borrow), requires Value(ys) <= Value(xs)
  //////////////////////////////////////////////////////////////////////////////

  // Subtract with an incoming borrow (0 or 1). Returns limbs of length |xs|
  // together with an outgoing borrow bout. The invariant:
  //   Value(xs) + bout * BASE^|xs|  ==  Value(ys) + bin + Value(zs)
  // Requires |ys| <= |xs| so ys aligns inside xs.
  function SubBorrowSpec(xs: seq<limb>, ys: seq<limb>, bin: limb): (res: (seq<limb>, limb))
    requires bin == 0 || bin == 1
    requires |ys| <= |xs|
    ensures var (zs, bout) := res;
            |zs| == |xs| && (bout == 0 || bout == 1)
    ensures var (zs, bout) := res;
            Value(xs) + L(bout) * Pow2_32(|xs|) == Value(ys) + L(bin) + Value(zs)
    decreases |xs|
  {
    if |xs| == 0 then
      ([], bin)
    else
      var xh: nat := L(xs[0]);
      var yh: nat := if |ys| == 0 then 0 else L(ys[0]);
      // true difference of this limb in int; borrow out iff it is negative
      var diff: int := xh - yh - L(bin);
      var need: limb := if diff >= 0 then 0 else 1;
      var lo: limb := (diff + L(need) * BASE) as limb;
      HeadSubDecompose(xs, ys, bin, lo, need);
      var yt := if |ys| == 0 then [] else ys[1..];
      var (rest, bout) := SubBorrowSpec(xs[1..], yt, need);
      SubBorrowStep(xs, ys, bin, lo, need, rest, bout);
      ([lo] + rest, bout)
  }

  // One subtraction limb: with xh,yh < BASE and bin in {0,1}, the true
  // difference xh - yh - bin lies in (-2*BASE, BASE); adding need*BASE (need the
  // borrow bit) lands it back in [0, BASE) and preserves the limb identity.
  lemma HeadSubDecompose(xs: seq<limb>, ys: seq<limb>, bin: limb,
                         lo: limb, need: limb)
    requires bin == 0 || bin == 1
    requires |xs| > 0
    requires var xh := L(xs[0]);
             var yh := if |ys| == 0 then 0 else L(ys[0]);
             var diff := xh - yh - L(bin);
             need == (if diff >= 0 then 0 else 1)
             && lo == (diff + L(need) * BASE) as limb
    ensures need == 0 || need == 1
    ensures L(xs[0]) + L(need) * BASE
          == (if |ys| == 0 then 0 else L(ys[0])) + L(bin) + L(lo)
  {
    // lo == xs[0] - yh - bin + need*BASE, rearrange to the ensures.
  }

  // Splice step for subtraction.
  lemma SubBorrowStep(xs: seq<limb>, ys: seq<limb>, bin: limb,
                      lo: limb, need: limb, rest: seq<limb>, bout: limb)
    requires bin == 0 || bin == 1
    requires need == 0 || need == 1
    requires bout == 0 || bout == 1
    requires |xs| > 0 && |ys| <= |xs|
    requires L(xs[0]) + L(need) * BASE
           == (if |ys| == 0 then 0 else L(ys[0])) + L(bin) + L(lo)
    requires var yt := if |ys| == 0 then [] else ys[1..];
             Value(xs[1..]) + L(bout) * Pow2_32(|xs| - 1) == Value(yt) + L(need) + Value(rest)
    ensures Value(xs) + L(bout) * Pow2_32(|xs|) == Value(ys) + L(bin) + Value([lo] + rest)
  {
    var yt := if |ys| == 0 then [] else ys[1..];
    assert ([lo] + rest)[0] == lo;
    assert ([lo] + rest)[1..] == rest;
    HeadTailValue(xs);
    HeadTailValue(ys);
    Pow2_32Positive(|xs| - 1);
    // Pow2_32(|xs|) == BASE * Pow2_32(|xs|-1)
    assert Pow2_32(|xs|) == BASE * Pow2_32(|xs| - 1);
    calc {
      Value(xs) + L(bout) * Pow2_32(|xs|);
      (L(xs[0]) + BASE * Value(xs[1..])) + L(bout) * (BASE * Pow2_32(|xs| - 1));
      { MulAssoc(L(bout), BASE, Pow2_32(|xs| - 1)); }
      L(xs[0]) + BASE * Value(xs[1..]) + (L(bout) * BASE) * Pow2_32(|xs| - 1);
      { assert (L(bout) * BASE) * Pow2_32(|xs|-1) == BASE * (L(bout) * Pow2_32(|xs|-1))
               by { MulAssoc(L(bout), BASE, Pow2_32(|xs|-1)); MulComm(L(bout), BASE); } }
      L(xs[0]) + BASE * Value(xs[1..]) + BASE * (L(bout) * Pow2_32(|xs| - 1));
      { MulDistrib(BASE, Value(xs[1..]), L(bout) * Pow2_32(|xs| - 1)); }
      L(xs[0]) + BASE * (Value(xs[1..]) + L(bout) * Pow2_32(|xs| - 1));
      L(xs[0]) + BASE * (Value(yt) + L(need) + Value(rest));
      { MulDistrib3(BASE, Value(yt), L(need), Value(rest)); }
      L(xs[0]) + BASE * Value(yt) + BASE * L(need) + BASE * Value(rest);
      { assert BASE * L(need) == L(need) * BASE by { MulComm(BASE, L(need)); } }
      (L(xs[0]) + L(need) * BASE) + BASE * Value(yt) + BASE * Value(rest);
      ((if |ys| == 0 then 0 else L(ys[0])) + L(bin) + L(lo)) + BASE * Value(yt) + BASE * Value(rest);
      ((if |ys| == 0 then 0 else L(ys[0])) + BASE * Value(yt)) + L(bin) + (L(lo) + BASE * Value(rest));
      Value(ys) + L(bin) + Value([lo] + rest);
    }
  }

  // Public subtraction: Value(ys) <= Value(xs) required.  Result normalized.
  function Sub(xs: seq<limb>, ys: seq<limb>): (zs: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    requires Value(ys) <= Value(xs)
    ensures Value(zs) == Value(xs) - Value(ys)
    ensures Normalized(zs)
  {
    LenFromValueLe(ys, xs);
    var (raw, bout) := SubBorrowSpec(xs, ys, 0);
    // Value(xs) + bout*BASE^|xs| == Value(ys) + Value(raw).  Since
    // Value(ys) <= Value(xs), and Value(raw) < BASE^|xs|, bout must be 0.
    SubNoFinalBorrow(xs, ys, raw, bout);
    Normalize(raw)
  }

  // With Value(ys) <= Value(xs), the final borrow is 0, so Value(raw) is exact.
  lemma SubNoFinalBorrow(xs: seq<limb>, ys: seq<limb>, raw: seq<limb>, bout: limb)
    requires |ys| <= |xs|
    requires bout == 0 || bout == 1
    requires |raw| == |xs|
    requires Value(xs) + L(bout) * Pow2_32(|xs|) == Value(ys) + Value(raw)
    requires Value(ys) <= Value(xs)
    ensures bout == 0
    ensures Value(raw) == Value(xs) - Value(ys)
  {
    ValueBound(raw);
    // If bout == 1: Value(xs) + BASE^|xs| == Value(ys) + Value(raw)
    //   => Value(raw) == Value(xs) - Value(ys) + BASE^|xs| >= BASE^|xs|,
    //      contradicting Value(raw) < BASE^|xs|.
    if bout == 1 {
      assert Value(raw) == Value(xs) - Value(ys) + Pow2_32(|xs|);
      assert Value(raw) >= Pow2_32(|xs|);
      assert false;
    }
  }

  // Normalized ys with Value(ys) <= Value(xs) has |ys| <= |xs|.
  lemma LenFromValueLe(ys: seq<limb>, xs: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    requires Value(ys) <= Value(xs)
    ensures |ys| <= |xs|
  {
    if |ys| > |xs| {
      CompareByLength(xs, ys);
      assert Value(xs) < Value(ys);
      assert false;
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Small nonlinear helper lemmas (localise nonlinear reasoning)
  //////////////////////////////////////////////////////////////////////////////

  lemma MulDistrib(a: nat, b: nat, c: nat)
    ensures a * (b + c) == a * b + a * c
  {}

  lemma MulDistrib3(a: nat, b: nat, c: nat, d: nat)
    ensures a * (b + c + d) == a * b + a * c + a * d
  {}

  lemma MulComm(a: nat, b: nat)
    ensures a * b == b * a
  {}

  lemma MulMonoRight(a: nat, b: nat, c: nat)
    requires b <= c
    ensures a * b <= a * c
  {}

  lemma MulMonoLeft(a: nat, b: nat, c: nat)
    requires a <= b
    ensures a * c <= b * c
  {}
}

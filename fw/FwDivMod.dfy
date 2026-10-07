/*******************************************************************************
 * dafny-bignum / fixed-width: FwDivMod
 *
 * Fixed-width Euclidean division/modulo. Mirrors the proven algorithm of
 * src/BigNatDivMod.dfy (recursive binary long division by halving), but every
 * executable value is a fixed-width newtype (limb) and no nat/int ever flows
 * through compiled code or as a method parameter (only ghost specs/lemmas use
 * nat). So the generated code stays Boost-free.
 *
 *   DivMod(xs, ys) = (q, r)  with  Value(xs) == Value(q)*Value(ys) + Value(r)
 *                                  and  Value(r) < Value(ys)   (ys != 0)
 *
 * BASEn is the ghost nat 2^32 (FwNat.BASE is the dword used in compiled code).
 *******************************************************************************/

include "FwNat.dfy"
include "FwSub.dfy"
include "FwCompare.dfy"

module FwDivMod {
  import opened FwNat
  import opened FwSub
  import opened FwCompare

  ghost const BASEn: nat := 0x1_0000_0000

  //////////////////////////////////////////////////////////////////////////////
  // Normalize: drop most-significant zero limbs. Executable; recurses on the
  // sequence, no numeric counter. Value-preserving, result Normalized.
  //////////////////////////////////////////////////////////////////////////////

  // LSB-first recursion, so no `|xs|-1` index is compiled (that index would be a
  // non-native int and fail the C++ Boost-free gate). Normalize the tail first;
  // if the tail is all-zero (empty) and the head is 0, the whole thing is 0.
  method Normalize(xs: seq<limb>) returns (zs: seq<limb>)
    ensures Normalized(zs)
    ensures Value(zs) == Value(xs)
    decreases |xs|
  {
    if |xs| == 0 {
      return [];
    }
    var tail := Normalize(xs[1..]);
    if |tail| == 0 && xs[0] == 0 {
      NormalizeAllZero(xs, tail);
      return [];
    }
    NormalizeConsHead(xs, tail);
    zs := [xs[0]] + tail;
  }

  // If the normalized tail is empty and the head is 0, Value(xs) == 0.
  lemma NormalizeAllZero(xs: seq<limb>, tail: seq<limb>)
    requires |xs| > 0 && |tail| == 0 && xs[0] == 0
    requires Value(tail) == Value(xs[1..])
    ensures Value(xs) == 0
  {
    assert Value(tail) == 0;
    assert Value(xs) == (xs[0] as nat) + BASEn * Value(xs[1..]);
  }

  // Prepending the head to the normalized tail: Value preserved, stays normalized
  // (the tail's top limb, if any, is nonzero; else the head itself is nonzero).
  lemma NormalizeConsHead(xs: seq<limb>, tail: seq<limb>)
    requires |xs| > 0
    requires Normalized(tail) && Value(tail) == Value(xs[1..])
    requires !(|tail| == 0 && xs[0] == 0)
    ensures Value([xs[0]] + tail) == Value(xs)
    ensures Normalized([xs[0]] + tail)
  {
    var zs := [xs[0]] + tail;
    assert zs[0] == xs[0] && zs[1..] == tail;
    assert Value(zs) == (xs[0] as nat) + BASEn * Value(tail);
    assert Value(xs) == (xs[0] as nat) + BASEn * Value(xs[1..]);
    // Normalized: if tail nonempty its last limb is tail's (nonzero); the last
    // limb of zs is the last of tail when |tail|>0, else zs==[xs[0]] with xs[0]!=0.
    if |tail| == 0 {
      assert zs == [xs[0]] && xs[0] != 0;
    } else {
      assert zs[|zs| - 1] == tail[|tail| - 1];
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Low bit of Value(xs).
  //////////////////////////////////////////////////////////////////////////////

  method LowBit(xs: seq<limb>) returns (b: limb)
    ensures b == 0 || b == 1
    ensures (b as nat) == Value(xs) % 2
  {
    if |xs| == 0 {
      return 0;
    }
    LowBitFromHead(xs);
    b := (xs[0] % 2);
  }

  lemma LowBitFromHead(xs: seq<limb>)
    requires |xs| > 0
    ensures Value(xs) % 2 == (xs[0] as nat) % 2
    ensures ((xs[0] % 2) as nat) == (xs[0] as nat) % 2
  {
    var rest := Value(xs[1..]);
    assert Value(xs) == (xs[0] as nat) + BASEn * rest;
    LemmaEvenMultiple(BASEn, rest);
    LemmaModAddMultiple((xs[0] as nat), BASEn * rest, 2);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Double: 2 * Value(v).
  //////////////////////////////////////////////////////////////////////////////

  method Double(v: seq<limb>) returns (zs: seq<limb>)
    ensures Normalized(zs)
    ensures Value(zs) == 2 * Value(v)
  {
    var d, c := AddSeq(v, v, 0);
    // AddSeq: Value(v)+Value(v)+0 == Value(d) + c*Pow32(|v|)
    var full := d + [c];
    AppendCarry(d, c, v);
    zs := Normalize(full);
  }

  // Value(d + [c]) == Value(d) + c*Pow32(|d|) == 2*Value(v) when the AddSeq
  // identity holds and |d|==|v|.
  lemma AppendCarry(d: seq<limb>, c: limb, v: seq<limb>)
    requires |d| == |v|
    requires Value(v) + Value(v) == Value(d) + (c as nat) * Pow32(|v|)
    ensures Value(d + [c]) == 2 * Value(v)
  {
    ValueAppend(d, c);
    assert Value(d + [c]) == Value(d) + Pow32(|d|) * (c as nat);
    assert Pow32(|d|) * (c as nat) == (c as nat) * Pow32(|v|) by { MulComm(Pow32(|d|), c as nat); }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Half: Value(xs) / 2, via most-significant-first halving with a carried bit.
  //////////////////////////////////////////////////////////////////////////////

  // Low bit falling out of HalfRec (ghost).
  ghost function LowBitAfter(xs: seq<limb>, hin: limb): nat
    requires hin == 0 || hin == 1
    decreases |xs|
  {
    if |xs| == 0 then (hin as nat)
    else
      var n := |xs| - 1;
      var full: nat := (hin as nat) * BASEn + (xs[n] as nat);
      LowBitAfter(xs[..n], (full % 2) as limb)
  }

  // Split a nonempty sequence into (all-but-last, last) by LSB-first recursion,
  // so no `|xs|-1` element index is compiled (which would be a non-native int).
  method SplitLast(xs: seq<limb>) returns (init: seq<limb>, last: limb)
    requires |xs| > 0
    ensures xs == init + [last]
    ensures |init| == |xs| - 1
    decreases |xs|
  {
    if |xs| == 1 {
      return [], xs[0];
    }
    var i2, l2 := SplitLast(xs[1..]);
    init := [xs[0]] + i2;
    last := l2;
    assert xs == [xs[0]] + xs[1..];
  }

  method HalfRec(xs: seq<limb>, hin: limb) returns (zs: seq<limb>)
    requires hin == 0 || hin == 1
    ensures |zs| == |xs|
    ensures 2 * Value(zs) == Value(xs) + (hin as nat) * Pow32(|xs|) - LowBitAfter(xs, hin)
    ensures LowBitAfter(xs, hin) == 0 || LowBitAfter(xs, hin) == 1
    decreases |xs|
  {
    if |xs| == 0 {
      return [];
    }
    // Split off the most-significant limb WITHOUT a compiled `|xs|-1` index
    // (that index is a non-native int and fails the Boost-free gate).
    var init, last := SplitLast(xs);
    ghost var n := |init|;        // ghost only: used by the proof lemmas below
    assert xs == init + [last] && xs[..n] == init && xs[n] == last;
    var full: dword := (hin as dword) * BASE + (last as dword);
    var q: limb := (full / 2) as limb;
    var hout: limb := (full % 2) as limb;
    HalfLimbBound(hin, last, full, q, hout);
    var lower := HalfRec(init, hout);
    // bridge facts where the recursive definitions live
    BridgeAppend(lower, q, n);
    BridgeValueTop(xs, n);
    assert (hout as nat) == ((hin as nat) * BASEn + (last as nat)) % 2;
    LowBitAfterUnfoldG(xs, hin, hout);
    LemmaPowStep(Pow32(n), n);
    HalfRecStep(xs, hin, q, hout, lower,
                Value(lower + [q]), Value(lower), Value(xs), Value(xs[..n]),
                Pow32(n), Pow32(|xs|),
                LowBitAfter(xs, hin), LowBitAfter(xs[..n], hout));
    zs := lower + [q];
  }

  // full = 2*q + hout with q < 2^32 and hout in {0,1}; q,hout computed in dword.
  lemma HalfLimbBound(hin: limb, x: limb, full: dword, q: limb, hout: limb)
    requires hin == 0 || hin == 1
    requires (full as nat) == (hin as nat) * BASEn + (x as nat)
    requires q == (full / 2) as limb
    requires hout == (full % 2) as limb
    ensures (q as nat) == (full as nat) / 2
    ensures (hout as nat) == (full as nat) % 2
    ensures hout == 0 || hout == 1
    ensures (full as nat) == 2 * (q as nat) + (hout as nat)
    ensures (q as nat) < BASEn
  {
    assert (full as nat) < 2 * BASEn;
    LemmaDivLt((full as nat), 2, BASEn);
    LemmaDivModIdentity((full as nat), 2);
  }

  lemma LowBitAfterUnfoldG(xs: seq<limb>, hin: limb, hout: limb)
    requires |xs| > 0
    requires hin == 0 || hin == 1
    requires hout == (((hin as nat) * BASEn + (xs[|xs| - 1] as nat)) % 2) as limb
    ensures LowBitAfter(xs, hin) == LowBitAfter(xs[..|xs| - 1], hout)
  {
  }

  lemma BridgeAppend(lower: seq<limb>, q: limb, n: nat)
    requires |lower| == n
    ensures Value(lower + [q]) == Value(lower) + Pow32(n) * (q as nat)
  {
    ValueAppend(lower, q);
  }

  lemma BridgeValueTop(xs: seq<limb>, n: nat)
    requires |xs| > 0 && n == |xs| - 1
    ensures Value(xs) == Value(xs[..n]) + Pow32(n) * (xs[n] as nat)
  {
    ValueAppend(xs[..n], xs[n]);
    assert xs[..n] + [xs[n]] == xs;
  }

  lemma HalfRecStep(xs: seq<limb>, hin: limb, q: limb, hout: limb,
                    lower: seq<limb>,
                    vApp: nat, vLow: nat, vXs: nat, vLo: nat,
                    pow: nat, powN: nat, lbTop: nat, lbLo: nat)
    requires |xs| > 0
    requires hin == 0 || hin == 1
    requires hout == 0 || hout == 1
    requires 2 * (q as nat) + (hout as nat) == (hin as nat) * BASEn + (xs[|xs| - 1] as nat)
    requires |lower| == |xs| - 1
    requires vApp == vLow + pow * (q as nat)
    requires vXs == vLo + pow * (xs[|xs| - 1] as nat)
    requires lbTop == lbLo
    requires pow * BASEn == powN
    requires 2 * vLow == vLo + (hout as nat) * pow - lbLo
    requires lbLo <= vLo + (hout as nat) * pow
    ensures 2 * vApp == vXs + (hin as nat) * powN - lbTop
  {
    HalfRecArith(vXs, vLo, vLow, pow,
                 (hin as nat), (hout as nat), (q as nat), (xs[|xs| - 1] as nat),
                 (hin as nat) * BASEn + (xs[|xs| - 1] as nat), lbLo, BASEn, powN);
  }

  // Pure-nat nonlinear algebra of HalfRecStep. lb cancels structurally.
  lemma HalfRecArith(vxs: nat, vlo: nat, vlow: nat, pow: nat,
                     hin: nat, hout: nat, q: nat, xn: nat, full: nat,
                     lb: nat, B: nat, powNext: nat)
    requires full == hin * B + xn
    requires full == 2 * q + hout
    requires vxs == vlo + pow * xn
    requires 2 * vlow == vlo + hout * pow - lb
    requires lb <= vlo + hout * pow
    requires powNext == pow * B
    ensures 2 * (vlow + pow * q) == vxs + hin * powNext - lb
  {
    calc {
      2 * (vlow + pow * q);
      { LemmaDistrib2(2, vlow, pow * q); }
      2 * vlow + 2 * (pow * q);
      { LemmaSwapMul(2, pow, q); }
      2 * vlow + pow * (2 * q);
      { assert 2 * vlow == vlo + hout * pow - lb; }
      (vlo + hout * pow - lb) + pow * (2 * q);
      { assert hout * pow == pow * hout by { MulComm(hout, pow); }
        LemmaDistrib2(pow, hout, 2 * q); }
      vlo + pow * (hout + 2 * q) - lb;
      { assert hout + 2 * q == full; }
      vlo + pow * full - lb;
      { LemmaDistrib2(pow, hin * B, xn); }
      vlo + pow * (hin * B) + pow * xn - lb;
      { assert vlo + pow * xn == vxs; }
      vxs + pow * (hin * B) - lb;
      { LemmaSwap2(pow, hin, B); }
      vxs + hin * (pow * B) - lb;
      { assert pow * B == powNext; }
      vxs + hin * powNext - lb;
    }
  }

  lemma LemmaSwap2(pow: nat, hin: nat, B: nat)
    ensures pow * (hin * B) == hin * (pow * B)
  {
    MulAssoc(pow, hin, B);
    MulAssoc(hin, pow, B);
    assert pow * hin == hin * pow by { MulComm(pow, hin); }
  }

  // Public Half.
  method Half(xs: seq<limb>) returns (zs: seq<limb>)
    ensures Normalized(zs)
    ensures Value(zs) == Value(xs) / 2
    ensures 2 * Value(zs) + (Value(xs) % 2) == Value(xs)
  {
    var raw := HalfRec(xs, 0);
    HalfTopHinZero(xs);
    LemmaHalfExact(Value(xs), Value(raw));
    zs := Normalize(raw);
  }

  lemma HalfTopHinZero(xs: seq<limb>)
    ensures LowBitAfter(xs, 0) == Value(xs) % 2
    decreases |xs|
  {
    HalfTopHinZeroAux(xs, 0);
  }

  lemma HalfTopHinZeroAux(xs: seq<limb>, hin: limb)
    requires hin == 0 || hin == 1
    ensures LowBitAfter(xs, hin) == (Value(xs) + (hin as nat) * Pow32(|xs|)) % 2
    decreases |xs|
  {
    if |xs| == 0 {
      assert Pow32(0) == 1;
      assert Value(xs) == 0;
      assert LowBitAfter(xs, hin) == (hin as nat);
      ModSmall((hin as nat), 2);
    } else {
      var n := |xs| - 1;
      var full: nat := (hin as nat) * BASEn + (xs[n] as nat);
      var hout := (full % 2) as limb;
      ParityFull(hin, xs[n], full, hout);
      HalfTopHinZeroAux(xs[..n], hout);
      ParityCombine(xs, hin, full, hout, n);
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // DivMod.
  //////////////////////////////////////////////////////////////////////////////

  method DivMod(xs: seq<limb>, ys: seq<limb>) returns (q: seq<limb>, r: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    requires Value(ys) > 0
    ensures Normalized(q) && Normalized(r)
    ensures Value(xs) == Value(q) * Value(ys) + Value(r)
    ensures Value(r) < Value(ys)
    decreases Value(xs)
  {
    var cmp := Compare(xs, ys);
    if cmp < 0 {
      LemmaMulZeroQ(Value(ys));
      return [], xs;
    }
    // Value(xs) >= Value(ys) > 0
    var h := Half(xs);
    HalfDecreases(xs, ys);
    var q1, r1 := DivMod(h, ys);
    var bit := LowBit(xs);
    var dr1 := Double(r1);
    var bitseq: seq<limb> := [bit];
    assert Value(bitseq) == (bit as nat);
    var r2 := AddFull(dr1, bitseq);              // 2*r1 + bit
    DoubleRemainderBound(r1, ys, bit, r2);
    var cmp2 := Compare(r2, ys);
    if cmp2 >= 0 {
      var dq1 := Double(q1);
      var one: seq<limb> := [1];
      assert Value(one) == 1;
      var qq := AddFull(dq1, one);               // 2*q1 + 1
      var rr, br := SubNormalized(r2, ys);         // r2 - Value(ys)
      FoldSubNat(Value(xs), Value(h), Value(q1), Value(ys), Value(r1), (bit as nat),
                 Value(r2), Value(qq), Value(rr));
      return qq, rr;
    } else {
      var qq := Double(q1);                        // 2*q1
      FoldNoSubNat(Value(xs), Value(h), Value(q1), Value(ys), Value(r1), (bit as nat),
                   Value(r2), Value(qq));
      return qq, r2;
    }
  }

  // Add two (not necessarily equal-length) sequences: zero-pad to equal length,
  // AddSeq, APPEND the final carry so the full sum is preserved, then Normalize.
  // Result: Value(zs) == Value(xs) + Value(ys), no dropped carry.
  method AddFull(xs: seq<limb>, ys: seq<limb>) returns (zs: seq<limb>)
    ensures Normalized(zs)
    ensures Value(zs) == Value(xs) + Value(ys)
  {
    var a, b := PadEqual(xs, ys);
    var s, c := AddSeq(a, b, 0);
    // s + [c] has value Value(s) + c*Pow32(|s|) == Value(a)+Value(b)
    AddFullProof(xs, ys, a, b, s, c);
    zs := Normalize(s + [c]);
  }

  ghost function MaxLen(xs: seq<limb>, ys: seq<limb>): nat
  { if |xs| >= |ys| then |xs| else |ys| }

  lemma AddFullProof(xs: seq<limb>, ys: seq<limb>, a: seq<limb>, b: seq<limb>,
                     s: seq<limb>, c: limb)
    requires |a| == |b| == MaxLen(xs, ys)
    requires |s| == |a|
    requires Value(a) == Value(xs) && Value(b) == Value(ys)
    requires Value(a) + Value(b) + 0 == Value(s) + (c as nat) * Pow32(|a|)
    ensures Value(s + [c]) == Value(xs) + Value(ys)
  {
    ValueAppend(s, c);
    assert Value(s + [c]) == Value(s) + Pow32(|s|) * (c as nat);
    assert Pow32(|s|) * (c as nat) == (c as nat) * Pow32(|a|) by { MulComm(Pow32(|s|), c as nat); }
  }

  // Pad both sequences to equal length (the max) with high zero limbs. Recurses
  // on the pair of sequences; no numeric counter in compiled code.
  method PadEqual(xs: seq<limb>, ys: seq<limb>) returns (a: seq<limb>, b: seq<limb>)
    ensures |a| == |b| == MaxLen(xs, ys)
    ensures Value(a) == Value(xs) && Value(b) == Value(ys)
    decreases |xs| + |ys|
  {
    if |xs| == 0 {
      a := ZeroPad(ys);
      b := ys;
      assert Value(a) == 0 == Value(xs);
      return;
    }
    if |ys| == 0 {
      a := xs;
      b := ZeroPad(xs);
      return;
    }
    // both nonempty: peel the low limb off each, recurse, prepend.
    var at, bt := PadEqual(xs[1..], ys[1..]);
    a := [xs[0]] + at;
    b := [ys[0]] + bt;
    PadPrepend(xs, ys, at, bt, a, b);
  }

  // A sequence of |s| zero limbs; Value 0, carried in the postcondition.
  method ZeroPad(s: seq<limb>) returns (z: seq<limb>)
    ensures |z| == |s|
    ensures Value(z) == 0
    decreases |s|
  {
    if |s| == 0 {
      return [];
    }
    var rest := ZeroPad(s[1..]);
    z := [0 as limb] + rest;
    assert z[0] == 0 && z[1..] == rest;
    assert Value(z) == (0 as nat) + 0x1_0000_0000 * Value(rest);
  }

  @IsolateAssertions
  lemma PadPrepend(xs: seq<limb>, ys: seq<limb>, at: seq<limb>, bt: seq<limb>,
                   a: seq<limb>, b: seq<limb>)
    requires |xs| > 0 && |ys| > 0
    requires |at| == |bt| == MaxLen(xs[1..], ys[1..])
    requires Value(at) == Value(xs[1..]) && Value(bt) == Value(ys[1..])
    requires a == [xs[0]] + at && b == [ys[0]] + bt
    ensures |a| == |b| == MaxLen(xs, ys)
    ensures Value(a) == Value(xs) && Value(b) == Value(ys)
  {
    MaxLenPeel(xs, ys);
    HeadSplit(a, xs[0], at);
    HeadSplit(xs, xs[0], xs[1..]);
    HeadSplit(b, ys[0], bt);
    HeadSplit(ys, ys[0], ys[1..]);
  }

  // Value of a head-prepended sequence, isolated (no MaxLen in scope).
  lemma HeadSplit(s: seq<limb>, h: limb, t: seq<limb>)
    requires |s| > 0 && s[0] == h && s[1..] == t
    ensures Value(s) == (h as nat) + 0x1_0000_0000 * Value(t)
  {}

  // MaxLen over the tails is one less than over the full sequences. Proved on
  // the plain lengths (|xs[1..]| == |xs|-1) so there is no sequence reasoning.
  lemma MaxLenPeel(xs: seq<limb>, ys: seq<limb>)
    requires |xs| > 0 && |ys| > 0
    ensures MaxLen(xs, ys) == MaxLen(xs[1..], ys[1..]) + 1
  {
    assert |xs[1..]| == |xs| - 1;
    assert |ys[1..]| == |ys| - 1;
  }

  // Subtract ys from xs when Value(ys) <= Value(xs); result normalized.
  method SubNormalized(xs: seq<limb>, ys: seq<limb>) returns (zs: seq<limb>, bout: limb)
    requires Value(ys) <= Value(xs)
    ensures Normalized(zs)
    ensures Value(zs) == Value(xs) - Value(ys)
    ensures bout == 0
  {
    var a, b := PadEqual(xs, ys);
    var d, br := SubSeq(a, b, 0);
    SubNormProof(xs, ys, a, b, d, br);
    zs := Normalize(d);
    bout := 0;
  }

  @IsolateAssertions
  lemma SubNormProof(xs: seq<limb>, ys: seq<limb>, a: seq<limb>, b: seq<limb>,
                     d: seq<limb>, br: limb)
    requires |a| == |b| == MaxLen(xs, ys)
    requires |d| == |a|
    requires Value(a) == Value(xs) && Value(b) == Value(ys)
    requires Value(ys) <= Value(xs)
    requires Value(a) + (br as nat) * Pow32(|a|) == Value(b) + 0 + Value(d)
    requires br == 0 || br == 1
    ensures Value(d) == Value(xs) - Value(ys)
    ensures br == 0
  {
    ValueBoundG(d);                          // Value(d) < Pow32(|d|) == Pow32(|a|)
    Pow32Positive(|a|);
    if br == 1 {
      // Value(a) + Pow32(|a|) == Value(b) + Value(d)
      // => Value(d) == Value(a) - Value(b) + Pow32(|a|) >= Pow32(|a|) > Value(d)
      assert Value(a) + Pow32(|a|) == Value(b) + Value(d);
      assert Value(a) >= Value(b);
      assert Value(d) >= Pow32(|a|);
      assert Value(d) < Pow32(|a|);          // contradiction
    }
    // br == 0: Value(a) == Value(b) + Value(d), so Value(d) == Value(a)-Value(b).
  }

  lemma ValueBoundG(xs: seq<limb>)
    ensures Value(xs) < Pow32(|xs|)
  {
    if |xs| == 0 {
    } else {
      ValueBoundG(xs[1..]);
      assert Value(xs) == (xs[0] as nat) + BASEn * Value(xs[1..]);
      assert Value(xs[1..]) <= Pow32(|xs| - 1) - 1;
      assert Pow32(|xs|) == BASEn * Pow32(|xs| - 1);
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Fold lemmas (pure nat), ported from src/BigNatDivMod.dfy.
  //////////////////////////////////////////////////////////////////////////////

  lemma DoubleRemainderBound(r1: seq<limb>, ys: seq<limb>, bit: limb, r2: seq<limb>)
    requires bit == 0 || bit == 1
    requires Value(r2) == 2 * Value(r1) + (bit as nat)
    requires Value(r1) < Value(ys)
    ensures Value(r2) < 2 * Value(ys)
  {
  }

  lemma FoldSubNat(vx: nat, vh: nat, vq1: nat, vy: nat, vr1: nat, bit: nat,
                   r2: nat, vq: nat, vr: nat)
    requires vh == vq1 * vy + vr1
    requires vx == 2 * vh + bit
    requires r2 == 2 * vr1 + bit
    requires r2 >= vy
    requires vq == 2 * vq1 + 1
    requires vr == r2 - vy
    ensures vx == vq * vy + vr
  {
    assert vx == 2 * (vq1 * vy + vr1) + bit;
    FoldArithSub(vx, vq1, vy, vr1, bit, r2, vr);
  }

  lemma FoldNoSubNat(vx: nat, vh: nat, vq1: nat, vy: nat, vr1: nat, bit: nat,
                     r2: nat, vq: nat)
    requires vh == vq1 * vy + vr1
    requires vx == 2 * vh + bit
    requires r2 == 2 * vr1 + bit
    requires r2 < vy
    requires vq == 2 * vq1
    ensures vx == vq * vy + r2
  {
    assert vx == 2 * (vq1 * vy + vr1) + bit;
    FoldArithNoSub(vx, vq1, vy, vr1, bit, r2);
  }

  lemma FoldArithSub(vx: nat, vq1: nat, vy: nat, vr1: nat, bit: nat, r2: nat, vr: nat)
    requires vx == 2 * (vq1 * vy + vr1) + bit
    requires r2 == 2 * vr1 + bit
    requires vr == r2 - vy
    requires r2 >= vy
    ensures vx == (2 * vq1 + 1) * vy + vr
  {
    calc {
      vx;
      2 * (vq1 * vy + vr1) + bit;
      { LemmaDistrib2(2, vq1 * vy, vr1); }
      2 * (vq1 * vy) + (2 * vr1 + bit);
      { LemmaSwapMul(2, vq1, vy); }
      (2 * vq1) * vy + r2;
      (2 * vq1) * vy + vy + vr;
      { LemmaMulPlusOne(2 * vq1, vy); }
      (2 * vq1 + 1) * vy + vr;
    }
  }

  lemma FoldArithNoSub(vx: nat, vq1: nat, vy: nat, vr1: nat, bit: nat, r2: nat)
    requires vx == 2 * (vq1 * vy + vr1) + bit
    requires r2 == 2 * vr1 + bit
    ensures vx == (2 * vq1) * vy + r2
  {
    calc {
      vx;
      2 * (vq1 * vy + vr1) + bit;
      { LemmaDistrib2(2, vq1 * vy, vr1); }
      2 * (vq1 * vy) + (2 * vr1 + bit);
      { LemmaSwapMul(2, vq1, vy); }
      (2 * vq1) * vy + r2;
    }
  }

  lemma HalfDecreases(xs: seq<limb>, ys: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    requires Value(ys) > 0
    requires Value(xs) >= Value(ys)
    ensures Value(xs) / 2 < Value(xs)
  {
    assert Value(xs) >= 1;
    LemmaHalfLt(Value(xs));
  }

  //////////////////////////////////////////////////////////////////////////////
  // Parity helpers (ported).
  //////////////////////////////////////////////////////////////////////////////

  lemma ParityFull(hin: limb, x: limb, full: nat, hout: limb)
    requires hin == 0 || hin == 1
    requires full == (hin as nat) * BASEn + (x as nat)
    requires hout == (full % 2) as limb
    ensures (hout as nat) == full % 2
    ensures hout == 0 || hout == 1
  {
    LemmaDivModIdentity(full, 2);
  }

  lemma ParityCombine(xs: seq<limb>, hin: limb, full: nat, hout: limb, n: nat)
    requires |xs| > 0 && n == |xs| - 1
    requires hin == 0 || hin == 1
    requires hout == 0 || hout == 1
    requires full == (hin as nat) * BASEn + (xs[n] as nat)
    requires (hout as nat) == full % 2
    requires LowBitAfter(xs[..n], hout) == (Value(xs[..n]) + (hout as nat) * Pow32(n)) % 2
    ensures LowBitAfter(xs, hin) == (Value(xs) + (hin as nat) * Pow32(|xs|)) % 2
  {
    Pow32Positive(n);
    LowBitAfterUnfoldG(xs, hin, hout);
    BridgeValueTop(xs, n);
    LemmaPowStep(Pow32(n), n);
    assert Pow32(n + 1) == Pow32(|xs|);
    ParityCombineNat(LowBitAfter(xs, hin), LowBitAfter(xs[..n], hout),
                     Value(xs), Value(xs[..n]), (hin as nat), (hout as nat),
                     (xs[n] as nat), full, Pow32(n), Pow32(|xs|));
  }

  lemma ParityCombineNat(lbTop: nat, lbLo: nat, vxs: nat, vlo: nat,
                         hin: nat, hout: nat, xn: nat, full: nat,
                         pow: nat, powXs: nat)
    requires full == hin * BASEn + xn
    requires hout == full % 2
    requires pow >= 1
    requires powXs == pow * BASEn
    requires lbTop == lbLo
    requires lbLo == (vlo + hout * pow) % 2
    requires vxs == vlo + pow * xn
    ensures lbTop == (vxs + hin * powXs) % 2
  {
    ParityCombineArith(vlo, xn, hin, hout, full, pow, BASEn);
    assert pow * xn == xn * pow by { MulComm(pow, xn); }
    assert vxs + hin * powXs == vlo + xn * pow + hin * (pow * BASEn);
  }

  lemma ParityCombineArith(V: nat, x: nat, hin: nat, hout: nat, full: nat,
                           P: nat, B: nat)
    requires B == BASEn
    requires full == hin * B + x
    requires hout == full % 2
    requires P >= 1
    ensures (V + hout * P) % 2 == (V + x * P + hin * (P * B)) % 2
  {
    assert hin * (P * B) == (hin * B) * P by { LemmaSwap(hin, P, B); }
    assert hin * B == full - x;
    assert x * P + (full - x) * P == full * P by { LemmaFactorP(x, full, P); }
    assert x * P + hin * (P * B) == full * P;
    LemmaDivModIdentity(full, 2);
    assert full == 2 * (full / 2) + hout;
    assert full * P == 2 * ((full / 2) * P) + hout * P by {
      LemmaFactorP2(full / 2, hout, P);
    }
    ModDropEven(V + hout * P, (full / 2) * P);
    assert V + full * P == (V + hout * P) + 2 * ((full / 2) * P);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Small arithmetic helpers (ported from src).
  //////////////////////////////////////////////////////////////////////////////

  lemma ValueAppend(xs: seq<limb>, x: limb)
    ensures Value(xs + [x]) == Value(xs) + Pow32(|xs|) * (x as nat)
    decreases |xs|
  {
    if |xs| == 0 {
      assert xs + [x] == [x];
      assert Value([x]) == (x as nat);
    } else {
      assert (xs + [x])[0] == xs[0];
      assert (xs + [x])[1..] == xs[1..] + [x];
      ValueAppend(xs[1..], x);
      var B := 0x1_0000_0000;
      assert Value(xs + [x]) == (xs[0] as nat) + B * Value(xs[1..] + [x]);
      assert Pow32(|xs|) == B * Pow32(|xs| - 1);
      ValueAppendAlg(B, xs[0] as nat, Value(xs[1..]), Pow32(|xs| - 1), x as nat);
    }
  }

  lemma ValueAppendAlg(B: nat, h: nat, vt: nat, p: nat, x: nat)
    ensures h + B * (vt + p * x) == (h + B * vt) + (B * p) * x
  {}

  lemma LemmaDistrib2(a: nat, p: nat, q: nat)
    ensures a * (p + q) == a * p + a * q
  {}

  lemma LemmaSwapMul(a: nat, p: nat, q: nat)
    ensures a * (p * q) == (a * p) * q
  {
    MulAssoc(a, p, q);
  }

  lemma LemmaMulPlusOne(a: nat, b: nat)
    ensures a * b + b == (a + 1) * b
  {}

  lemma LemmaMulZeroQ(b: nat)
    ensures 0 * b == 0
  {}

  lemma LemmaDivLt(full: nat, two: nat, bound: nat)
    requires two == 2
    requires full < two * bound
    ensures full / two < bound
  {
    if full / two >= bound {
      LemmaMulMonoB(bound, full / two, two);
      assert bound * two == two * bound by { MulComm(bound, two); }
    }
  }

  lemma LemmaMulMonoB(a: nat, b: nat, k: nat)
    requires a <= b
    ensures a * k <= b * k
  {}

  lemma LemmaPowStep(pow: nat, n: nat)
    requires pow == Pow32(n)
    ensures pow * 0x1_0000_0000 == Pow32(n + 1)
  {
    assert Pow32(n + 1) == 0x1_0000_0000 * Pow32(n);
    MulComm(0x1_0000_0000, pow);
  }

  lemma LemmaHalfExact(v: nat, half: nat)
    requires 2 * half == v - (v % 2)
    ensures half == v / 2
    ensures 2 * half + (v % 2) == v
  {
    LemmaDivModIdentity(v, 2);
  }

  lemma LemmaHalfLt(v: nat)
    requires v >= 1
    ensures v / 2 < v
  {}

  lemma LemmaDivModIdentity(s: nat, b: nat)
    requires b > 0
    ensures s == (s / b) * b + s % b
    ensures 0 <= s % b < b
  {}

  lemma LemmaEvenMultiple(b: nat, k: nat)
    requires b % 2 == 0
    ensures (b * k) % 2 == 0
  {
    assert b == 2 * (b / 2);
    assert b * k == 2 * ((b / 2) * k) by { MulAssoc(2, b / 2, k); }
  }

  lemma LemmaModAddMultiple(a: nat, m: nat, two: nat)
    requires two == 2
    requires m % two == 0
    ensures (a + m) % two == a % two
  {}

  lemma ModSmall(a: nat, m: nat)
    requires 0 <= a < m
    ensures a % m == a
  {}

  lemma LemmaSwap(a: nat, p: nat, b: nat)
    ensures a * (p * b) == (a * b) * p
  {
    MulAssoc(a, p, b);
    MulAssoc(a, b, p);
    assert p * b == b * p by { MulComm(p, b); }
  }

  lemma LemmaFactorP(x: nat, full: nat, P: nat)
    requires x <= full
    ensures x * P + (full - x) * P == full * P
  {
    LemmaMulMonoB2(x, full - x, P);
  }

  lemma LemmaMulMonoB2(a: nat, b: nat, k: nat)
    ensures a * k + b * k == (a + b) * k
  {}

  lemma LemmaFactorP2(h: nat, hout: nat, P: nat)
    ensures (2 * h + hout) * P == 2 * (h * P) + hout * P
  {
    LemmaMulMonoB2(2 * h, hout, P);
    LemmaSwapMul(2, h, P);
  }

  lemma ModDropEven(a: nat, k: nat)
    ensures (a + 2 * k) % 2 == a % 2
  {}
}

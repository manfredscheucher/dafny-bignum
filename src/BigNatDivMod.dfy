/*******************************************************************************
 * dafny-bignum: BigNatDivMod
 *
 * Verified Euclidean division/modulo of unsigned BigNats (base 2^32 limbs),
 * specified against BigNat.Value.
 *
 *   DivMod(xs, ys) = (q, r)  with  Value(xs) == Value(q)*Value(ys) + Value(r)
 *                                  and  Value(r) < Value(ys)   (ys != 0)
 *
 * Algorithm: plain binary long division expressed by halving the dividend.
 * Writing  Value(xs) = 2*Value(Half(xs)) + bit,  recursively divide Half(xs),
 * then fold the low bit back in with at most one subtraction of the divisor.
 * No quotient estimation, no 128-bit reasoning -- only Compare / Add / Sub from
 * BigNatAddSub plus a verified Half primitive, each proved against Value.
 *******************************************************************************/

include "BigNat.dfy"
include "BigNatAddSub.dfy"

module BigNatDivMod {

  import opened BigNat
  import opened BigNatAddSub

  //////////////////////////////////////////////////////////////////////////////
  // Low bit and halving of a limb sequence, specified against Value.
  //////////////////////////////////////////////////////////////////////////////

  // The least significant bit of Value(xs).
  function LowBit(xs: seq<limb>): (b: limb)
    ensures b == 0 || b == 1
    ensures L(b) == Value(xs) % 2
  {
    if |xs| == 0 then 0
    else
      LowBitFromHead(xs);
      (L(xs[0]) % 2) as limb
  }

  // Value(xs) % 2 is decided by the least significant limb, since BASE is even.
  lemma LowBitFromHead(xs: seq<limb>)
    requires |xs| > 0
    ensures Value(xs) % 2 == L(xs[0]) % 2
  {
    // Value(xs) == L(xs[0]) + BASE*Value(xs[1..]), BASE even, so same parity.
    var rest := Value(xs[1..]);
    assert Value(xs) == L(xs[0]) + BASE * rest;
    assert BASE % 2 == 0;
    LemmaEvenMultiple(BASE, rest);
    assert (BASE * rest) % 2 == 0;
    LemmaModAddMultiple(L(xs[0]), BASE * rest, 2);
  }

  // Half(xs): the limb sequence denoting Value(xs) / 2.  Processes limbs from the
  // most significant end, carrying the dropped low bit of each limb down into
  // the next.  hin is the bit entering from above (0 at the top).
  function HalfRec(xs: seq<limb>, hin: limb): (zs: seq<limb>)
    requires hin == 0 || hin == 1
    ensures |zs| == |xs|
    ensures 2 * Value(zs) == Value(xs) + L(hin) * Pow2_32(|xs|) - LowBitAfter(xs, hin)
    ensures LowBitAfter(xs, hin) == 0 || LowBitAfter(xs, hin) == 1
    decreases |xs|
  {
    if |xs| == 0 then
      []
    else
      var n := |xs| - 1;
      // full value entering this (top) limb position from above plus this limb
      var full: nat := L(hin) * BASE + L(xs[n]);
      var q: limb := (full / 2) as limb;
      var hout: limb := (full % 2) as limb;
      HalfLimbBound(hin, xs[n], full, q, hout);
      var lower := HalfRec(xs[..n], hout);
      // Establish the four bridge equalities here, where the recursive
      // definitions live, then bind every recursive term and hand the nats to
      // HalfRecStep (which has no recursion in scope).
      BridgeAppend(lower, q, n);
      BridgeValueTop(xs, n);
      assert hout == ((L(hin) * BASE + L(xs[n])) % 2) as limb;
      LowBitAfterUnfold(xs, hin, hout);
      LemmaPowStep(Pow2_32(n), n);
      HalfRecStep(xs, hin, full, q, hout, lower,
                  Value(lower + [q]), Value(lower), Value(xs), Value(xs[..n]),
                  Pow2_32(n), Pow2_32(|xs|),
                  LowBitAfter(xs, hin), LowBitAfter(xs[..n], hout));
      lower + [q]
  }

  // The bit that falls out at the bottom of HalfRec, i.e. Value(xs) with hin on
  // top, taken mod 2.  Equivalently the overall low bit of the shifted value.
  function LowBitAfter(xs: seq<limb>, hin: limb): nat
    requires hin == 0 || hin == 1
    decreases |xs|
  {
    if |xs| == 0 then L(hin)
    else
      var n := |xs| - 1;
      var full: nat := L(hin) * BASE + L(xs[n]);
      LowBitAfter(xs[..n], (full % 2) as limb)
  }

  // Per-limb split: full = 2*q + hout with q < BASE and hout in {0,1}.
  lemma HalfLimbBound(hin: limb, x: limb, full: nat, q: limb, hout: limb)
    requires hin == 0 || hin == 1
    requires full == L(hin) * BASE + L(x)
    requires q == (full / 2) as limb
    requires hout == (full % 2) as limb
    ensures L(q) == full / 2
    ensures L(hout) == full % 2
    ensures hout == 0 || hout == 1
    ensures full == 2 * L(q) + L(hout)
    ensures L(q) < BASE
  {
    // full <= 1*BASE + (BASE-1) = 2*BASE-1 < 2*BASE, hence full/2 < BASE.
    assert full < 2 * BASE;
    LemmaDivLt(full, 2, BASE);
  }

  // One-step unfolding of LowBitAfter at a nonempty sequence, isolated so the
  // definitional fact is proved cheaply on its own rather than inside the full
  // nonlinear context of HalfRecStep (where it timed out).
  lemma LowBitAfterUnfold(xs: seq<limb>, hin: limb, hout: limb)
    requires |xs| > 0
    requires hin == 0 || hin == 1
    requires hout == ((L(hin) * BASE + L(xs[|xs| - 1])) % 2) as limb
    ensures LowBitAfter(xs, hin) == LowBitAfter(xs[..|xs| - 1], hout)
  {
    // Direct from the definition of LowBitAfter at |xs| > 0.
  }

  // Fold the top-limb split into the Value recurrence for HalfRec.
  //
  // The body never touches the recursive functions (Value, LowBitAfter): the
  // caller binds each to a local and passes it in, so the heavy nonlinear
  // algebra in HalfRecArith runs over plain nats with no definitions to unfold.
  // The four bridge equalities (append of lower, top-limb split of xs, the
  // LowBitAfter unfolding, and the power step) are established by the caller via
  // dedicated helpers, then handed in as nat hypotheses here.
  lemma HalfRecStep(xs: seq<limb>, hin: limb, full: nat, q: limb, hout: limb,
                    lower: seq<limb>,
                    vApp: nat, vLow: nat, vXs: nat, vLo: nat,
                    pow: nat, powN: nat, lbTop: nat, lbLo: nat)
    requires |xs| > 0
    requires hin == 0 || hin == 1
    requires hout == 0 || hout == 1
    requires full == L(hin) * BASE + L(xs[|xs| - 1])
    requires full == 2 * L(q) + L(hout)
    requires |lower| == |xs| - 1
    // bridge hypotheses, all nat (no recursion left in scope)
    requires vApp == vLow + pow * L(q)
    requires vXs == vLo + pow * L(xs[|xs| - 1])
    requires lbTop == lbLo
    requires pow * BASE == powN
    requires 2 * vLow == vLo + L(hout) * pow - lbLo
    requires lbLo <= vLo + L(hout) * pow
    ensures 2 * vApp == vXs + L(hin) * powN - lbTop
  {
    HalfRecArith(vXs, vLo, vLow, pow,
                 L(hin), L(hout), L(q), L(xs[|xs| - 1]), full, lbLo, BASE, powN);
  }

  // vApp == vLow + Pow2_32(n) * L(q), with the sequence append confined here.
  lemma BridgeAppend(lower: seq<limb>, q: limb, n: nat)
    requires |lower| == n
    ensures Value(lower + [q]) == Value(lower) + Pow2_32(n) * L(q)
  {
    ValueAppend(lower, q);
  }

  // Value(xs) == Value(xs[..n]) + Pow2_32(n) * L(xs[n]), append confined here.
  lemma BridgeValueTop(xs: seq<limb>, n: nat)
    requires |xs| > 0 && n == |xs| - 1
    ensures Value(xs) == Value(xs[..n]) + Pow2_32(n) * L(xs[n])
  {
    ValueAppend(xs[..n], xs[n]);
    assert xs[..n] + [xs[n]] == xs;
  }

  // All the nonlinear algebra of HalfRecStep, over plain naturals.  lb is the
  // dropped low bit, treated as an opaque constant (it cancels structurally).
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
    // 2*(vlow + pow*q) == 2*vlow + 2*pow*q == (vlo + hout*pow - lb) + pow*(2*q)
    //   == vlo + pow*(hout + 2*q) - lb == vlo + pow*full - lb
    //   == vlo + pow*(hin*B + xn) - lb == vlo + pow*xn + pow*(hin*B) - lb
    //   == vxs + hin*(pow*B) - lb == vxs + hin*powNext - lb.
    calc {
      2 * (vlow + pow * q);
      { LemmaDistrib2(2, vlow, pow * q); }
      2 * vlow + 2 * (pow * q);
      { LemmaSwapMul(2, pow, q); }                 // 2*(pow*q) == pow*(2*q)
      2 * vlow + pow * (2 * q);
      { assert 2 * vlow == vlo + hout * pow - lb; }
      (vlo + hout * pow - lb) + pow * (2 * q);
      { assert hout * pow == pow * hout by { MulComm(hout, pow); }
        LemmaDistrib2(pow, hout, 2 * q); }         // pow*hout + pow*(2q) == pow*(hout+2q)
      vlo + pow * (hout + 2 * q) - lb;
      { assert hout + 2 * q == full; }
      vlo + pow * full - lb;
      { LemmaDistrib2(pow, hin * B, xn); }         // pow*(hin*B + xn) == pow*(hin*B) + pow*xn
      vlo + pow * (hin * B) + pow * xn - lb;
      { assert vlo + pow * xn == vxs; }
      vxs + pow * (hin * B) - lb;
      { LemmaSwap2(pow, hin, B); }                 // pow*(hin*B) == hin*(pow*B)
      vxs + hin * (pow * B) - lb;
      { assert pow * B == powNext; }
      vxs + hin * powNext - lb;
    }
  }

  // pow*(hin*B) == hin*(pow*B)
  lemma LemmaSwap2(pow: nat, hin: nat, B: nat)
    ensures pow * (hin * B) == hin * (pow * B)
  {
    MulAssoc(pow, hin, B);     // pow*(hin*B) == (pow*hin)*B
    MulAssoc(hin, pow, B);     // hin*(pow*B) == (hin*pow)*B
    assert pow * hin == hin * pow by { MulComm(pow, hin); }
  }

  // Public Half: Value(Half(xs)) == Value(xs) / 2.
  function Half(xs: seq<limb>): (zs: seq<limb>)
    ensures 2 * Value(zs) + (Value(xs) % 2) == Value(xs)
    ensures Value(zs) == Value(xs) / 2
  {
    var raw := HalfRec(xs, 0);
    HalfTopHinZero(xs);
    // 2*Value(raw) == Value(xs) - LowBitAfter(xs,0), and LowBitAfter(xs,0)==Value(xs)%2
    LemmaHalfExact(Value(xs), Value(raw));
    Normalize(raw)
  }

  // With hin = 0 the dropped bit equals Value(xs) % 2.
  lemma HalfTopHinZero(xs: seq<limb>)
    ensures LowBitAfter(xs, 0) == Value(xs) % 2
    decreases |xs|
  {
    if |xs| == 0 {
    } else {
      var n := |xs| - 1;
      var full: nat := 0 * BASE + L(xs[n]);
      assert full == L(xs[n]);
      // Not needed to fully unfold; parity propagates. Use the direct identity
      // via the Value recurrence instead.
      HalfTopHinZeroAux(xs, 0);
    }
  }

  // General: LowBitAfter(xs, hin) == (Value(xs) + hin*BASE^|xs|) % 2.  Since BASE
  // is even, this is just (Value(xs) + 0) % 2 = Value(xs)%2 when hin==0, but we
  // prove the general parity statement by induction.
  lemma HalfTopHinZeroAux(xs: seq<limb>, hin: limb)
    requires hin == 0 || hin == 1
    ensures LowBitAfter(xs, hin) == (Value(xs) + L(hin) * Pow2_32(|xs|)) % 2
    decreases |xs|
  {
    if |xs| == 0 {
      assert Pow2_32(0) == 1;
      assert Value(xs) == 0;
      assert LowBitAfter(xs, hin) == L(hin);
      assert L(hin) == (0 + L(hin) * 1) % 2 by { ModSmall(L(hin), 2); }
    } else {
      var n := |xs| - 1;
      var full: nat := L(hin) * BASE + L(xs[n]);
      var hout := (full % 2) as limb;
      ParityFull(hin, xs[n], full, hout);
      HalfTopHinZeroAux(xs[..n], hout);
      ParityCombine(xs, hin, full, hout, n);
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Division via halving recursion.
  //////////////////////////////////////////////////////////////////////////////

  // DivMod(xs, ys): quotient and remainder of Value(xs) by Value(ys) (ys != 0).
  function DivMod(xs: seq<limb>, ys: seq<limb>): (res: (seq<limb>, seq<limb>))
    requires Normalized(xs) && Normalized(ys)
    requires Value(ys) > 0
    ensures var (q, r) := res;
            Normalized(q) && Normalized(r)
    ensures var (q, r) := res;
            Value(xs) == Value(q) * Value(ys) + Value(r)
    ensures var (q, r) := res;
            Value(r) < Value(ys)
    decreases Value(xs)
  {
    if Compare(xs, ys) < 0 then
      // Value(xs) < Value(ys): quotient 0, remainder xs.
      LemmaMulZeroQ(Value(ys));
      ([], xs)
    else
      // Value(xs) >= Value(ys) > 0, so Value(xs) > 0 and Half strictly decreases.
      var h := Half(xs);
      HalfDecreases(xs, ys);
      var (q1, r1) := DivMod(h, ys);
      // Reconstruct: Value(xs) = 2*Value(h) + bit.
      var bit := LowBit(xs);
      var r2 := Add(Double(r1), [bit]);   // 2*r1 + bit, in [0, 2*Value(ys))
      DoubleRemainderBound(r1, ys, bit, r2);
      if Compare(r2, ys) >= 0 then
        var q := Add(Double(q1), One);    // 2*q1 + 1
        var r := Sub(r2, ys);             // r2 - Value(ys)
        FoldSubNat(Value(xs), Value(h), Value(q1), Value(ys), Value(r1), L(bit),
                   Value(r2), Value(q), Value(r));
        (q, r)
      else
        var q := Double(q1);              // 2*q1
        FoldNoSubNat(Value(xs), Value(h), Value(q1), Value(ys), Value(r1), L(bit),
                     Value(r2), Value(q));
        (q, r2)
  }

  // Double(v) = 2 * Value(v), normalized.
  function Double(v: seq<limb>): (zs: seq<limb>)
    ensures Normalized(zs)
    ensures Value(zs) == 2 * Value(v)
  {
    var d := Add(v, v);
    assert Value(d) == Value(v) + Value(v);
    assert Value(v) + Value(v) == 2 * Value(v);
    d
  }

  // 2*r1 + bit < 2*Value(ys) when Value(r1) < Value(ys) and bit in {0,1}.
  lemma DoubleRemainderBound(r1: seq<limb>, ys: seq<limb>, bit: limb, r2: seq<limb>)
    requires bit == 0 || bit == 1
    requires Value(r2) == 2 * Value(r1) + L(bit)
    requires Value(r1) < Value(ys)
    ensures Value(r2) < 2 * Value(ys)
  {
    // 2*Value(r1) <= 2*(Value(ys)-1) = 2*Value(ys)-2, +bit <= 2*Value(ys)-1.
  }

  // Fold step, subtraction branch: r2 >= Value(ys).
  // Pure-nat algebra of the fold steps, so the nonlinear multiplication is
  // proved without any Value(...) recursion in scope. Mirrors HalfRecArith.
  //   subtraction branch:  vx == (2*vq1+1)*vy + vr   when vx == 2*vq1*vy + r2,
  //                         r2 == vr + vy
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

  //   no-subtraction branch:  vx == (2*vq1)*vy + r2   when vx == 2*vq1*vy + r2
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

  // Fold steps are now pure-nat lemmas with NO Value() and NO product of two
  // variables in their signature: the dividend-partition is handed in as the
  // single opaque nat `vh` (standing for Value(h) == vq1*vy + vr1), and the
  // product vq1*vy is the caller's job to relate to vh. This keeps every
  // verification condition linear, so Z3 never enters the nonlinear search that
  // made the old seq/Value wrappers time out. Caller: DivMod (see below).
  //
  // subtraction branch: vq == 2*vq1+1, vr == r2 - vy.
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

  // no-subtraction branch: vq == 2*vq1, remainder r2.
  lemma FoldNoSubNat(vx: nat, vh: nat, vq1: nat, vy: nat, vr1: nat, bit: nat,
                     r2: nat, vq: nat)
    requires vh == vq1 * vy + vr1
    requires vx == 2 * vh + bit
    requires r2 == 2 * vr1 + bit
    requires vq == 2 * vq1
    ensures vx == vq * vy + r2
  {
    assert vx == 2 * (vq1 * vy + vr1) + bit;
    FoldArithNoSub(vx, vq1, vy, vr1, bit, r2);
  }

  // When Value(xs) >= Value(ys) > 0, Value(Half(xs)) < Value(xs).
  lemma HalfDecreases(xs: seq<limb>, ys: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    requires Value(ys) > 0
    requires Compare(xs, ys) >= 0
    ensures Value(Half(xs)) < Value(xs)
  {
    // Compare(xs,ys) >= 0 ==> Value(xs) >= Value(ys) >= 1, so Value(xs) >= 1.
    assert Value(xs) >= Value(ys);
    assert Value(xs) >= 1;
    // Value(Half(xs)) == Value(xs)/2 < Value(xs) for Value(xs) >= 1.
    LemmaHalfLt(Value(xs));
  }

  //////////////////////////////////////////////////////////////////////////////
  // Small arithmetic / modular helper lemmas (localise nonlinear reasoning).
  //////////////////////////////////////////////////////////////////////////////

  lemma LemmaDistrib2(a: nat, p: nat, q: nat)
    ensures a * (p + q) == a * p + a * q
  {}

  lemma MulComm(a: nat, b: nat)
    ensures a * b == b * a
  {}

  // 2*(p*q) == (2*p)*q  (and the pow variant), via associativity/commutativity.
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

  // full/2 < BASE from full < 2*BASE.
  lemma LemmaDivLt(full: nat, two: nat, bound: nat)
    requires two == 2
    requires full < two * bound
    ensures full / two < bound
  {
    if full / two >= bound {
      LemmaMulMonoB(bound, full / two, two);
      assert (full / two) * two >= bound * two;
      assert full >= (full / two) * two;   // Euclid: full == (full/2)*2 + full%2
      assert bound * two == two * bound by { MulComm(bound, two); }
    }
  }

  lemma LemmaMulMonoB(a: nat, b: nat, k: nat)
    requires a <= b
    ensures a * k <= b * k
  {}

  // pow == Pow2_32(n), ensures pow*BASE == Pow2_32(n+1) == Pow2_32(|xs|) where
  // |xs| == n+1.
  lemma LemmaPowStep(pow: nat, n: nat)
    requires pow == Pow2_32(n)
    ensures pow * BASE == Pow2_32(n + 1)
  {
    // Pow2_32(n+1) == BASE * Pow2_32(n) == BASE * pow == pow * BASE.
    assert Pow2_32(n + 1) == BASE * Pow2_32(n);
    MulComm(BASE, pow);
  }

  // From 2*half == v - v%2 (half == v/2) and v given.
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

  // Parity: BASE even ==> (a + BASE*k) % 2 == a % 2.
  lemma LemmaEvenMultiple(b: nat, k: nat)
    requires b % 2 == 0
    ensures (b * k) % 2 == 0
  {
    // b == 2*(b/2), so b*k == 2*((b/2)*k).
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

  // full == hin*BASE + L(x); hout == full%2; proves hout == (L(x))%2 since BASE
  // even -- but we keep it general: hout == full % 2 directly.
  lemma ParityFull(hin: limb, x: limb, full: nat, hout: limb)
    requires hin == 0 || hin == 1
    requires full == L(hin) * BASE + L(x)
    requires hout == (full % 2) as limb
    ensures L(hout) == full % 2
    ensures hout == 0 || hout == 1
  {
    LemmaDivModIdentity(full, 2);
  }

  // Combine step for HalfTopHinZeroAux.
  // Thin wrapper: bind every recursive term (LowBitAfter, Value) and the powers
  // to locals where the definitions live, establish the bridge facts via small
  // helpers, then hand the plain nats to ParityCombineNat (no recursion, no
  // Value in scope) which carries the nonlinear modular algebra. Same shape as
  // HalfRec -> HalfRecStep.
  lemma ParityCombine(xs: seq<limb>, hin: limb, full: nat, hout: limb, n: nat)
    requires |xs| > 0 && n == |xs| - 1
    requires hin == 0 || hin == 1
    requires hout == 0 || hout == 1
    requires full == L(hin) * BASE + L(xs[n])
    requires L(hout) == full % 2
    requires LowBitAfter(xs[..n], hout) == (Value(xs[..n]) + L(hout) * Pow2_32(n)) % 2
    ensures LowBitAfter(xs, hin) == (Value(xs) + L(hin) * Pow2_32(|xs|)) % 2
  {
    // Bridge facts, each confined to a helper where the recursion unfolds.
    Pow2_32Positive(n);
    LowBitAfterUnfold(xs, hin, hout);                 // lbTop == lbLo
    BridgeValueTop(xs, n);                            // vxs == vlo + pow*L(xs[n])
    LemmaPowStep(Pow2_32(n), n);                      // pow*BASE == Pow2_32(|xs|)
    assert Pow2_32(n + 1) == Pow2_32(|xs|);
    ParityCombineNat(LowBitAfter(xs, hin), LowBitAfter(xs[..n], hout),
                     Value(xs), Value(xs[..n]), L(hin), L(hout), L(xs[n]),
                     full, Pow2_32(n), Pow2_32(|xs|));
  }

  // Pure-nat core of ParityCombine. No Value/LowBitAfter, no recursion: the
  // caller supplies lbTop, lbLo, vxs, vlo and the powers as plain nats.
  lemma ParityCombineNat(lbTop: nat, lbLo: nat, vxs: nat, vlo: nat,
                         hin: nat, hout: nat, xn: nat, full: nat,
                         pow: nat, powXs: nat)
    requires full == hin * BASE + xn
    requires hout == full % 2
    requires pow >= 1
    requires powXs == pow * BASE
    requires lbTop == lbLo
    requires lbLo == (vlo + hout * pow) % 2
    requires vxs == vlo + pow * xn
    ensures lbTop == (vxs + hin * powXs) % 2
  {
    // (vlo + hout*pow) % 2 == (vlo + xn*pow + hin*(pow*BASE)) % 2  (ParityCombineArith)
    ParityCombineArith(vlo, xn, hin, hout, full, pow, BASE);
    // vxs + hin*powXs == vlo + pow*xn + hin*(pow*BASE); and pow*xn == xn*pow.
    assert pow * xn == xn * pow by { MulComm(pow, xn); }
    assert vxs + hin * powXs == vlo + xn * pow + hin * (pow * BASE);
  }

  // The modular arithmetic behind ParityCombine, over plain nats.
  //   full == hin*B + x,  hout == full % 2
  //   (V + hout*P) % 2 == (V + x*P + hin*(P*B)) % 2
  // Uses: P even?  No -- P == BASE^n may be odd only when n==0 (P==1). We instead
  // reduce via hout ≡ full (mod 2) and full == hin*B + x with B even.
  lemma ParityCombineArith(V: nat, x: nat, hin: nat, hout: nat, full: nat,
                           P: nat, B: nat)
    requires B == BASE
    requires full == hin * B + x
    requires hout == full % 2
    requires P >= 1
    ensures (V + hout * P) % 2 == (V + x * P + hin * (P * B)) % 2
  {
    // hin*(P*B) == (hin*B)*P, and hin*B == full - x, so
    //   x*P + hin*(P*B) == x*P + (full-x)*P == full*P.
    assert hin * (P * B) == (hin * B) * P by { LemmaSwap(hin, P, B); }
    assert hin * B == full - x;
    assert x * P + (full - x) * P == full * P by { LemmaFactorP(x, full, P); }
    assert x * P + hin * (P * B) == full * P;
    // So RHS == (V + full*P) % 2.  Now full == 2*(full/2) + hout, so
    //   full*P == 2*(full/2)*P + hout*P,  the first term even.
    LemmaDivModIdentity(full, 2);
    assert full == 2 * (full / 2) + hout;
    assert full * P == (2 * (full / 2) + hout) * P by {}
    assert full * P == 2 * ((full / 2) * P) + hout * P by {
      LemmaFactorP2(full / 2, hout, P);
    }
    // (V + full*P) % 2 == (V + hout*P + 2*(...)) % 2 == (V + hout*P) % 2.
    ModDropEven(V + hout * P, (full / 2) * P);
    assert V + full * P == (V + hout * P) + 2 * ((full / 2) * P);
  }

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
    LemmaMulMonoB2(2 * h, hout, P);        // (2h)*P + hout*P == (2h+hout)*P
    LemmaSwapMul(2, h, P);                 // (2*h)*P == 2*(h*P)
  }

  lemma ModDropEven(a: nat, k: nat)
    ensures (a + 2 * k) % 2 == a % 2
  {}
}

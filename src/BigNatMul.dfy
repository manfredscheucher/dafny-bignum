/*******************************************************************************
 * dafny-bignum: verified arbitrary-precision arithmetic in pure Dafny.
 *
 * BigNatMul: verified multiplication of unsigned BigNats (base 2^32 limbs).
 *
 * Strategy (schoolbook): recurse over the multiplier ys.
 *   Value(xs) * Value(ys) = Value(xs)*L(ys[0]) + BASE * (Value(xs)*Value(ys[1..]))
 * so MulRaw(xs, ys) = AddSeq( MulLimb(xs, ys[0]), Shift1( MulRaw(xs, ys[1..]) ) ).
 *
 * All arithmetic is plain nat arithmetic (limbs are a nat-backed newtype in
 * BigNat.dfy). A single carry step computes s = a + b*... in nat and splits it
 * into a low limb (s % BASE) and a carry limb (s / BASE). No bitvectors are
 * used, which keeps the SMT solver fast.
 *
 * AddSeq is defined locally here (not imported from the add/sub module) so this
 * file verifies against BigNat.dfy alone.
 *******************************************************************************/

include "BigNat.dfy"

module BigNatMul {

  import opened BigNat

  //////////////////////////////////////////////////////////////////////////////
  // Limb split: carve a nat into a low limb (mod BASE) and carry limb (div BASE).
  //////////////////////////////////////////////////////////////////////////////

  // For the single carry step we need: given s < BASE*BASE, s/BASE < BASE so the
  // carry fits in a limb, and s = (s/BASE)*BASE + s%BASE with s%BASE < BASE.
  lemma LemmaSplit(s: nat)
    requires s < BASE * BASE
    ensures s / BASE < BASE
    ensures s % BASE < BASE
    ensures s == (s / BASE) * BASE + s % BASE
  {
    LemmaDivModIdentity(s, BASE);
    LemmaDivLtQuotient(s, BASE, BASE);
  }

  // Euclidean identity s == (s/b)*b + s%b for b > 0.
  lemma LemmaDivModIdentity(s: nat, b: nat)
    requires b > 0
    ensures s == (s / b) * b + s % b
    ensures 0 <= s % b < b
  {}

  // If s < q*b then s/b < q (for b > 0, q > 0).
  lemma LemmaDivLtQuotient(s: nat, b: nat, q: nat)
    requires b > 0 && q > 0
    requires s < q * b
    ensures s / b < q
  {
    if s / b >= q {
      // s/b >= q  ==>  (s/b)*b >= q*b  ==>  s >= q*b, contradiction
      LemmaMulMono(q, s / b, b);
      assert (s / b) * b >= q * b;
      LemmaDivModIdentity(s, b);
      assert s >= (s / b) * b;
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Local limb-wise addition (self-contained; not the public Add module).
  //////////////////////////////////////////////////////////////////////////////

  function AddSeq(xs: seq<limb>, ys: seq<limb>): (zs: seq<limb>)
    ensures Value(zs) == Value(xs) + Value(ys)
  {
    AddSeqC(xs, ys, 0)
  }

  // Add with an incoming carry limb c (0 or 1).
  function AddSeqC(xs: seq<limb>, ys: seq<limb>, c: limb): (zs: seq<limb>)
    requires c == 0 || c == 1
    ensures Value(zs) == Value(xs) + Value(ys) + L(c)
    decreases |xs| + |ys|
  {
    if |xs| == 0 && |ys| == 0 then
      (if c == 0 then [] else [c])
    else
      var x0: limb := if |xs| == 0 then 0 else xs[0];
      var y0: limb := if |ys| == 0 then 0 else ys[0];
      var xtail := if |xs| == 0 then [] else xs[1..];
      var ytail := if |ys| == 0 then [] else ys[1..];
      // sum of two limbs plus a carry bit: < BASE + BASE = 2*BASE < BASE*BASE
      var s: nat := L(x0) + L(y0) + L(c);
      LemmaAddSumBound(x0, y0, c, s);
      var d: limb := (s % BASE) as limb;
      var cout: limb := (s / BASE) as limb;
      LemmaAddCarryBit(s);
      var rest := AddSeqC(xtail, ytail, cout);
      LemmaAddStep(xs, ys, c, d, rest, s, cout, x0, y0, xtail, ytail);
      [d] + rest
  }

  // The three-limb sum is < BASE*BASE, so the split is valid, and here the
  // carry is in fact 0 or 1 because the sum is < 2*BASE.
  lemma LemmaAddSumBound(x0: limb, y0: limb, c: limb, s: nat)
    requires c == 0 || c == 1
    requires s == L(x0) + L(y0) + L(c)
    ensures s < 2 * BASE
    ensures s < BASE * BASE
  {
    assert L(x0) < BASE && L(y0) < BASE && L(c) <= 1;
    LemmaBaseBig();
  }

  lemma LemmaBaseBig()
    ensures 2 * BASE < BASE * BASE
  {
    LemmaMulMono(2, BASE, BASE);
  }

  // Carry-out of an add step is 0 or 1 (sum < 2*BASE), and the split holds.
  lemma LemmaAddCarryBit(s: nat)
    requires s < 2 * BASE
    ensures (s / BASE) as int == 0 || (s / BASE) as int == 1
    ensures 0 <= s / BASE < BASE
    ensures 0 <= s % BASE < BASE
    ensures s == (s / BASE) * BASE + s % BASE
  {
    LemmaBaseBig();
    LemmaSplit(s);
    LemmaDivLtQuotient(s, BASE, 2);
  }

  // Recursion step for AddSeqC.
  lemma LemmaAddStep(xs: seq<limb>, ys: seq<limb>, c: limb, d: limb,
                     rest: seq<limb>, s: nat, cout: limb,
                     x0: limb, y0: limb, xtail: seq<limb>, ytail: seq<limb>)
    requires (|xs| == 0 ==> x0 == 0 && xtail == []) && (|xs| > 0 ==> x0 == xs[0] && xtail == xs[1..])
    requires (|ys| == 0 ==> y0 == 0 && ytail == []) && (|ys| > 0 ==> y0 == ys[0] && ytail == ys[1..])
    requires s == L(x0) + L(y0) + L(c)
    requires L(d) + BASE * L(cout) == s
    requires Value(rest) == Value(xtail) + Value(ytail) + L(cout)
    ensures Value([d] + rest) == Value(xs) + Value(ys) + L(c)
  {
    assert ([d] + rest)[0] == d;
    assert ([d] + rest)[1..] == rest;
    LemmaValueHead(xs, x0, xtail);
    LemmaValueHead(ys, y0, ytail);
    assert Value(xs) == L(x0) + BASE * Value(xtail);
    assert Value(ys) == L(y0) + BASE * Value(ytail);
    LemmaDistrib3(BASE, Value(xtail), Value(ytail), L(cout));
    assert BASE * (Value(xtail) + Value(ytail) + L(cout))
        == BASE * Value(xtail) + BASE * Value(ytail) + BASE * L(cout);
    assert Value([d] + rest) == L(d) + BASE * Value(rest);
    // L(d) + BASE*L(cout) == s == L(x0)+L(y0)+L(c)
  }

  // Value(xs) == L(head) + BASE*Value(tail), covering the empty case.
  lemma LemmaValueHead(xs: seq<limb>, head: limb, tail: seq<limb>)
    requires (|xs| == 0 ==> head == 0 && tail == [])
    requires (|xs| > 0 ==> head == xs[0] && tail == xs[1..])
    ensures Value(xs) == L(head) + BASE * Value(tail)
  {
  }

  lemma LemmaDistrib3(a: nat, p: nat, q: nat, r: nat)
    ensures a * (p + q + r) == a * p + a * q + a * r
  {
  }

  //////////////////////////////////////////////////////////////////////////////
  // Shift by one limb: prepend a zero limb, multiplying Value by BASE.
  //////////////////////////////////////////////////////////////////////////////

  function Shift1(xs: seq<limb>): (zs: seq<limb>)
    ensures Value(zs) == BASE * Value(xs)
  {
    if |xs| == 0 then []
    else
      assert ([0 as limb] + xs)[0] == 0 as limb;
      assert ([0 as limb] + xs)[1..] == xs;
      [0 as limb] + xs
  }

  //////////////////////////////////////////////////////////////////////////////
  // Single-limb scaling: multiply a limb-seq by one limb m.
  //////////////////////////////////////////////////////////////////////////////

  // MulLimbC(xs, m, c): (Value(xs) * L(m)) + L(c) as a limb-seq.
  function MulLimbC(xs: seq<limb>, m: limb, c: limb): (zs: seq<limb>)
    ensures Value(zs) == Value(xs) * L(m) + L(c)
    decreases |xs|
  {
    if |xs| == 0 then
      (if c == 0 then [] else [c])
    else
      var x0: limb := xs[0];
      // x0*m + c < BASE*BASE: x0*m <= (BASE-1)^2 and c <= BASE-1, sum < BASE*BASE
      var s: nat := L(x0) * L(m) + L(c);
      LemmaMulLimbBound(x0, m, c, s);
      var d: limb := (s % BASE) as limb;
      var cout: limb := (s / BASE) as limb;
      LemmaSplit(s);
      var rest := MulLimbC(xs[1..], m, cout);
      LemmaMulLimbStep(xs, m, c, x0, s, d, cout, rest);
      [d] + rest
  }

  function MulLimb(xs: seq<limb>, m: limb): (zs: seq<limb>)
    ensures Value(zs) == Value(xs) * L(m)
  {
    MulLimbC(xs, m, 0)
  }

  // x0*m + c < BASE*BASE.
  lemma LemmaMulLimbBound(x0: limb, m: limb, c: limb, s: nat)
    requires s == L(x0) * L(m) + L(c)
    ensures s < BASE * BASE
  {
    // L(x0) <= BASE-1, L(m) <= BASE-1 ==> L(x0)*L(m) <= (BASE-1)^2 = BASE*BASE - 2*BASE + 1
    LemmaMulUpper(L(x0), L(m), BASE - 1, BASE - 1);
    assert L(x0) * L(m) <= (BASE - 1) * (BASE - 1);
    LemmaSquareMinusOne();
    assert (BASE - 1) * (BASE - 1) == BASE * BASE - 2 * BASE + 1;
    assert L(c) <= BASE - 1;
  }

  // (BASE-1)*(BASE-1) == BASE*BASE - 2*BASE + 1
  lemma LemmaSquareMinusOne()
    ensures (BASE - 1) * (BASE - 1) == BASE * BASE - 2 * BASE + 1
  {
    var b := BASE;
    calc {
      (b - 1) * (b - 1);
      { LemmaMulDistribMinus(b - 1, b, 1); }
      (b - 1) * b - (b - 1) * 1;
      { LemmaMulDistribMinusLeft(b, 1, b); }
      b * b - 1 * b - (b - 1);
    }
  }

  lemma LemmaMulDistribMinus(a: nat, p: nat, q: nat)
    requires q <= p
    ensures a * (p - q) == a * p - a * q
  {}

  lemma LemmaMulDistribMinusLeft(p: nat, q: nat, a: nat)
    requires q <= p
    ensures (p - q) * a == p * a - q * a
  {}

  // If a <= amax and b <= bmax then a*b <= amax*bmax (naturals).
  lemma LemmaMulUpper(a: nat, b: nat, amax: nat, bmax: nat)
    requires a <= amax && b <= bmax
    ensures a * b <= amax * bmax
  {
    LemmaMulMono(a, amax, b);     // a*b <= amax*b
    LemmaMulMono(b, bmax, amax);  // b*amax <= bmax*amax
    assert amax * b == b * amax;
    assert bmax * amax == amax * bmax;
  }

  // Recursion step for MulLimbC.
  lemma LemmaMulLimbStep(xs: seq<limb>, m: limb, c: limb, x0: limb, s: nat,
                         d: limb, cout: limb, rest: seq<limb>)
    requires |xs| > 0
    requires x0 == xs[0]
    requires s == L(x0) * L(m) + L(c)
    requires L(d) + BASE * L(cout) == s
    requires Value(rest) == Value(xs[1..]) * L(m) + L(cout)
    ensures Value([d] + rest) == Value(xs) * L(m) + L(c)
  {
    assert ([d] + rest)[0] == d;
    assert ([d] + rest)[1..] == rest;
    var tail := xs[1..];
    var vt := Value(tail);
    assert Value([d] + rest) == L(d) + BASE * Value(rest);
    assert Value(rest) == vt * L(m) + L(cout);
    LemmaDistrib2(BASE, vt * L(m), L(cout));
    assert BASE * (vt * L(m) + L(cout)) == BASE * (vt * L(m)) + BASE * L(cout);
    LemmaShuffleMul(BASE, vt, L(m));
    assert BASE * (vt * L(m)) == (BASE * vt) * L(m);
    // Value([d]+rest) == L(d) + (BASE*vt)*L(m) + BASE*L(cout)
    //                 == (L(d)+BASE*L(cout)) + (BASE*vt)*L(m)
    //                 == s + (BASE*vt)*L(m)
    //                 == L(x0)*L(m) + L(c) + (BASE*vt)*L(m)
    LemmaFactorHead(L(x0), BASE, vt, L(m));
    assert L(x0) * L(m) + (BASE * vt) * L(m) == (L(x0) + BASE * vt) * L(m);
    assert Value(xs) == L(x0) + BASE * vt;
  }

  lemma LemmaDistrib2(a: nat, p: nat, q: nat)
    ensures a * (p + q) == a * p + a * q
  {
  }

  // BASE * (V * m) == (BASE * V) * m
  lemma LemmaShuffleMul(b: nat, v: nat, m: nat)
    ensures b * (v * m) == (b * v) * m
  {
    MulAssoc(b, v, m);
  }

  // (x0 + BASE*V) * m == x0*m + (BASE*V)*m
  lemma LemmaFactorHead(x0: nat, b: nat, v: nat, m: nat)
    ensures (x0 + b * v) * m == x0 * m + (b * v) * m
  {
  }

  lemma LemmaMulMono(a: nat, ab: nat, k: nat)
    requires a <= ab
    ensures a * k <= ab * k
  {
    LemmaMulMonoInd(ab - a, a, k);
  }

  lemma LemmaMulMonoInd(delta: nat, a: nat, k: nat)
    ensures (a + delta) * k == a * k + delta * k
  {
  }

  //////////////////////////////////////////////////////////////////////////////
  // Full multiplication.
  //////////////////////////////////////////////////////////////////////////////

  // Raw (not necessarily normalized) product; Value is exact.
  function MulRaw(xs: seq<limb>, ys: seq<limb>): (zs: seq<limb>)
    ensures Value(zs) == Value(xs) * Value(ys)
    decreases |ys|
  {
    if |ys| == 0 then
      assert Value(ys) == 0;
      LemmaMulZeroR(Value(xs));
      []
    else
      var partial := MulLimb(xs, ys[0]);          // Value(xs) * L(ys[0])
      var higher := MulRaw(xs, ys[1..]);          // Value(xs) * Value(ys[1..])
      var shifted := Shift1(higher);              // BASE * (Value(xs)*Value(ys[1..]))
      var zs := AddSeq(partial, shifted);
      LemmaMulSplit(xs, ys);
      zs
  }

  lemma LemmaMulZeroR(a: nat)
    ensures a * 0 == 0
  {
  }

  // Value(xs)*Value(ys) == Value(xs)*L(ys[0]) + BASE*(Value(xs)*Value(ys[1..]))
  lemma LemmaMulSplit(xs: seq<limb>, ys: seq<limb>)
    requires |ys| > 0
    ensures Value(xs) * Value(ys)
         == Value(xs) * L(ys[0]) + BASE * (Value(xs) * Value(ys[1..]))
  {
    var V := Value(xs);
    var y0 := L(ys[0]);
    var yt := Value(ys[1..]);
    assert Value(ys) == y0 + BASE * yt;
    calc {
      V * Value(ys);
      V * (y0 + BASE * yt);
      { LemmaDistrib2(V, y0, BASE * yt); }
      V * y0 + V * (BASE * yt);
      { LemmaSwap3(V, BASE, yt); }
      V * y0 + BASE * (V * yt);
    }
  }

  // V * (BASE * yt) == BASE * (V * yt)
  lemma LemmaSwap3(v: nat, b: nat, yt: nat)
    ensures v * (b * yt) == b * (v * yt)
  {
    MulAssoc(v, b, yt);   // v*(b*yt) == (v*b)*yt
    MulAssoc(b, v, yt);   // b*(v*yt) == (b*v)*yt
    assert v * b == b * v;
  }

  // Public multiplication: normalized result, exact Value.
  function Mul(xs: seq<limb>, ys: seq<limb>): (zs: seq<limb>)
    ensures Normalized(zs)
    ensures Value(zs) == Value(xs) * Value(ys)
  {
    Normalize(MulRaw(xs, ys))
  }
}

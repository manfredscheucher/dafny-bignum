/*******************************************************************************
 * dafny-bignum: Rational
 *
 * Arbitrary-precision rationals: a signed BigInt numerator over an unsigned,
 * strictly positive BigNat denominator. The sign lives in the numerator; the
 * denominator is always > 0. Specified against RatValue(), the real number
 * denoted.
 *
 * Make reduces to lowest terms by dividing numerator magnitude and denominator
 * by their gcd (exact division: the gcd divides both, so DivMod leaves no
 * remainder). add / sub / mul / compare follow the usual fraction identities
 * and reduce the result.
 *******************************************************************************/

include "PureArith.dfy"
include "BigNat.dfy"
include "BigNatAddSub.dfy"
include "BigNatMul.dfy"
include "BigNatDivMod.dfy"
include "BigNatGCD.dfy"
include "BigInt.dfy"

module Rational {
  import opened BigNat
  import BigNatAddSub
  import BigNatMul
  import BigNatDivMod
  import BigNatGCD
  import BigInt
  import PureArith

  // num / den, den > 0. Sign is carried by num.
  datatype Rat = Rat(num: BigInt.Int, den: seq<limb>)

  predicate Wf(x: Rat)
  {
    BigInt.Wf(x.num) && Normalized(x.den) && Value(x.den) > 0
  }

  // The real number denoted. den > 0 (from Wf) so the division is well defined.
  function RatValue(x: Rat): real
    requires Wf(x)
  {
    BigInt.IntValue(x.num) as real / Value(x.den) as real
  }

  //////////////////////////////////////////////////////////////////////////////
  // Cast bridge: Value-as-real of a product is the product of the real casts.
  // The field / nat reasoning lives in PureArith (no bignum axioms in scope).
  //////////////////////////////////////////////////////////////////////////////

  // Given the product fact vp == vx*vy (supplied by the caller from Mul's
  // postcondition, so no Mul/Value recursion enters this lemma), the real casts
  // multiply. Pure nat/real; delegates to PureArith.CastMul.
  lemma MulValueReal(vx: nat, vy: nat, vp: nat)
    requires vp == vx * vy
    ensures (vp as real) == (vx as real) * (vy as real)
  {
    PureArith.CastMul(vx, vy);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Constructors.
  //////////////////////////////////////////////////////////////////////////////

  // One over nothing reduced: num/den with den > 0, not reduced. Always Wf.
  function MakeRaw(num: BigInt.Int, den: seq<limb>): (r: Rat)
    requires BigInt.Wf(num) && Normalized(den) && Value(den) > 0
    ensures Wf(r)
    ensures RatValue(r) == BigInt.IntValue(num) as real / Value(den) as real
  {
    Rat(num, den)
  }

  // A whole number as a rational n/1.
  function FromInt(n: BigInt.Int): (r: Rat)
    requires BigInt.Wf(n)
    ensures Wf(r)
    ensures RatValue(r) == BigInt.IntValue(n) as real
  {
    ValueOne();
    assert Value(One) == 1;
    var r := Rat(n, One);
    assert RatValue(r) == BigInt.IntValue(n) as real / 1.0;
    r
  }

  // Smart constructor: reduce num/den to lowest terms via gcd of |num| and den.
  // Opaque: callers must not unfold the whole gcd reduction (doing so drags the
  // recursive bignum axioms into their context and blows up Z3); the value and
  // Wf postconditions below are all any caller needs.
  opaque function Make(num: BigInt.Int, den: seq<limb>): (res: Rat)
    requires BigInt.Wf(num) && Normalized(den) && Value(den) > 0
    ensures Wf(res)
    ensures RatValue(res) == BigInt.IntValue(num) as real / Value(den) as real
    // Canonical form: the result is in lowest terms (|num| and den coprime).
    ensures Coprime(Value(res.num.mag), Value(res.den))
  {
    var amag := num.mag;              // |num|, normalized
    // Shortcut: a zero numerator reduces to 0/1 with no gcd/division needed.
    // gcd(0, 1) == 1, so the canonical/coprime postcondition holds trivially.
    if amag == [] then
      ValueOne();
      ZeroOverOneCoprime();
      Rat(BigInt.Zero, One)
    else
    var g := BigNatGCD.GCD(amag, den);
    GcdDenPositive(amag, den, g);     // Value(g) > 0 (divides den > 0)
    // g divides both amag and den exactly.
    var (qa, ra) := BigNatDivMod.DivMod(amag, g);
    var (qd, rd) := BigNatDivMod.DivMod(den, g);
    // Bind every Value to a nat first. DivMod's postconditions become nat facts
    // over these locals; the two gcd-divides facts come from GCD's IsGCD post.
    var vn := Value(amag); var vqa := Value(qa); var vg := Value(g);
    var vd := Value(den); var vqd := Value(qd);
    var vra := Value(ra); var vrd := Value(rd);
    assert BigNatGCD.IsGCD(vg, vn, vd);
    // Zero remainders + qd > 0, all nonlinear reasoning confined to nat lemmas.
    ReduceExactDriver(vn, vd, vg, vqa, vra, vqd, vrd);
    // ra == rd == 0 turns DivMod's post into exact products by substitution.
    assert vn == vqa * vg;
    assert vd == vqd * vg;
    var newNum := BigInt.Make(num.negative, qa);
    var r := Rat(newNum, qd);
    // All the real-cast / cancellation algebra lives in its own lemma (a fresh,
    // small context) rather than inside this heavy function body.
    MakeRealStep(num, qa, g, den, qd, newNum, vn, vqa, vg, vd, vqd);
    assert Value(qd) == vqd;
    assert RatValue(r) == (BigInt.IntValue(newNum) as real) / (vqd as real);
    // Coprime: the quotients qa, qd are coprime because we divided by the gcd.
    CoprimeAfterDivide(vn, vd, vg, vqa, vqd);
    assert Value(r.num.mag) == vqa && Value(r.den) == vqd;
    r
  }

  // gcd(0, 1) == 1: the zero-numerator shortcut's result is coprime.
  lemma ZeroOverOneCoprime()
    ensures Coprime(0, 1)
  {
    assert BigNatGCD.DividesNat(1, 0) by { assert 0 == 1 * 0; }
    assert BigNatGCD.DividesNat(1, 1) by { assert 1 == 1 * 1; }
    forall d: nat | BigNatGCD.DividesNat(d, 0) && BigNatGCD.DividesNat(d, 1)
      ensures BigNatGCD.DividesNat(d, 1)
    {}
  }

  // The real-value equation for Make, isolated so its verification context is
  // small (Make itself is too heavy to also carry the IntValue/real unfolding).
  // Shows IntValue(newNum)/vqd == IntValue(num)/vd as reals.
  lemma MakeRealStep(num: BigInt.Int, qa: seq<limb>, g: seq<limb>, den: seq<limb>,
                     qd: seq<limb>, newNum: BigInt.Int,
                     vn: nat, vqa: nat, vg: nat, vd: nat, vqd: nat)
    requires BigInt.Wf(num)
    requires vn == Value(num.mag) && vqa == Value(qa) && vg == Value(g)
    requires vd == Value(den) && vqd == Value(qd)
    requires vg > 0 && vd > 0 && vqd > 0
    requires vn == vqa * vg && vd == vqd * vg
    requires Normalized(qa)
    requires newNum == BigInt.Make(num.negative, qa)
    ensures (BigInt.IntValue(newNum) as real) / (vqd as real)
            == (BigInt.IntValue(num) as real) / (vd as real)
  {
    var gr := vg as real; var qdr := vqd as real;
    var nn := BigInt.IntValue(newNum) as real;
    var no := BigInt.IntValue(num) as real;
    ReduceSign(num, qa, g, newNum, vn, vqa, vg);
    assert nn * gr == no;
    PureArith.CastProd(vd, vqd, vg);
    assert (vd as real) == qdr * gr;
    ReduceFracStep(nn, no, gr, qdr, vd as real);
  }

  // DividesNat(vg, n) is literally `exists k :: n == vg*k`. Unfolding it over
  // plain nats (no Value in sight) is cheap; doing it amid Value's recursive
  // axioms is not. This tiny bridge isolates that unfolding.
  lemma DividesExists(vg: nat, n: nat)
    requires BigNatGCD.DividesNat(vg, n)
    ensures exists k: nat :: n == vg * k
  {}

  // Nat-level driver: takes the already-bound nats plus the two gcd-divides
  // facts, hands everything to PureArith. Crucially this lemma's SIGNATURE and
  // body contain NO Value() and NO Value*Value product, so Z3 never pulls in the
  // recursive bignum axioms that make the nonlinear reasoning blow up.
  lemma ReduceExactDriver(va: nat, vd: nat, vg: nat,
                          vqa: nat, vra: nat, vqd: nat, vrd: nat)
    requires vg > 0 && vd > 0
    requires BigNatGCD.DividesNat(vg, va) && BigNatGCD.DividesNat(vg, vd)
    requires va == vqa * vg + vra && vra < vg
    requires vd == vqd * vg + vrd && vrd < vg
    ensures vra == 0 && vrd == 0
    ensures vqd > 0
  {
    DividesExists(vg, va);
    DividesExists(vg, vd);
    PureArith.ReduceExactNat(va, vd, vg, vqa, vra, vqd, vrd);
  }

  // Numerator and denominator are coprime iff their gcd is 1.
  ghost predicate Coprime(a: nat, b: nat) { BigNatGCD.IsGCD(1, a, b) }

  // Dividing both sides by g == gcd(va, vd) leaves coprime quotients: if
  // IsGCD(vg, va, vd), vg > 0, va == vqa*vg and vd == vqd*vg, then gcd(vqa,vqd)
  // is 1. Standard fact "a/gcd and b/gcd are coprime".
  lemma CoprimeAfterDivide(va: nat, vd: nat, vg: nat, vqa: nat, vqd: nat)
    requires vg > 0
    requires BigNatGCD.IsGCD(vg, va, vd)
    requires va == vqa * vg && vd == vqd * vg
    ensures Coprime(vqa, vqd)
  {
    // 1 divides everything, so the first two IsGCD conjuncts are immediate.
    assert BigNatGCD.DividesNat(1, vqa) by { assert vqa == 1 * vqa; }
    assert BigNatGCD.DividesNat(1, vqd) by { assert vqd == 1 * vqd; }
    // Any common divisor d of vqa and vqd: show d divides 1, i.e. d == 1.
    forall d: nat | BigNatGCD.DividesNat(d, vqa) && BigNatGCD.DividesNat(d, vqd)
      ensures BigNatGCD.DividesNat(d, 1)
    {
      // d | vqa  ==>  d*vg | vqa*vg == va;  likewise d*vg | vd.
      PureArith.DivMulRight(d, vqa, vg);
      assert BigNatGCD.DividesNat(d * vg, va) by { assert exists k: nat :: va == (d * vg) * k; }
      PureArith.DivMulRight(d, vqd, vg);
      assert BigNatGCD.DividesNat(d * vg, vd) by { assert exists k: nat :: vd == (d * vg) * k; }
      // d*vg is a common divisor of va, vd, so by IsGCD it divides vg.
      assert BigNatGCD.DividesNat(d * vg, vg);
      // d*vg | vg with vg > 0 forces d == 1.
      PureArith.DivisorOfFactorIsOne(d, vg);
      assert d == 1;
      assert BigNatGCD.DividesNat(d, 1) by { assert 1 == d * 1; }
    }
  }

  // Value(g) > 0: g divides den and den > 0, so g != 0.
  lemma GcdDenPositive(amag: seq<limb>, den: seq<limb>, g: seq<limb>)
    requires Normalized(amag) && Normalized(den) && Value(den) > 0
    requires g == BigNatGCD.GCD(amag, den)
    ensures Normalized(g) && Value(g) > 0
  {
    assert BigNatGCD.IsGCD(Value(g), Value(amag), Value(den));
    assert BigNatGCD.DividesNat(Value(g), Value(den));
    if Value(g) == 0 {
      // DividesNat(0, den) <==> den == 0, contradiction.
      assert exists k: nat :: Value(den) == 0 * k;
    }
  }

  // The real-cancellation step of Make, taking everything as reals/nats plus the
  // single integer bridge from ReduceSign. No Value() and no nat*nat product in
  // the signature, so Z3 stays stable. nn/no are the reduced/original numerators
  // as reals, gr == g, qdr == qd (all > 0 denominators), vdr == den.
  lemma ReduceFracStep(nn: real, no: real, gr: real, qdr: real, vdr: real)
    requires gr > 0.0 && qdr > 0.0
    requires vdr == qdr * gr          // den == qd * g
    requires no == nn * gr            // IntValue(num) == IntValue(newNum) * g
    ensures nn / qdr == no / vdr
  {
    PureArith.ReduceFracReal(nn, no, qdr, gr, vdr);
  }

  // IntValue(newNum) * g == IntValue(num), with newNum == Make(num.negative, qa)
  // and |num| == qa*g. The product |num| == qa*g is supplied as a pre-bound nat
  // hypothesis (vn == vqa*vg), so no Value() product sits in the signature.
  lemma ReduceSign(num: BigInt.Int, qa: seq<limb>, g: seq<limb>, newNum: BigInt.Int,
                   vn: nat, vqa: nat, vg: nat)
    requires BigInt.Wf(num)
    requires vn == Value(num.mag) && vqa == Value(qa) && vg == Value(g)
    requires vn == vqa * vg
    requires Normalized(qa)
    requires newNum == BigInt.Make(num.negative, qa)
    ensures (BigInt.IntValue(newNum) as real) * (vg as real)
            == BigInt.IntValue(num) as real
  {
    // Establish the two integer values and a common sign, then hand off all the
    // (nonlinear, real) algebra to PureArith.SignCastMul.
    var iNew := BigInt.IntValue(newNum);
    var iOld := BigInt.IntValue(num);
    assert Value(newNum.mag) == vqa;        // Make normalizes qa (already normal)
    if vqa == 0 {
      // Both numerator and reduced numerator are zero.
      assert iNew == 0 && iOld == 0;
      PureArith.SignCastMul(iNew, iOld, vqa, vg, vn, false);
    } else {
      // Nonzero: both carry num.negative.
      assert iNew == (if num.negative then -(vqa as int) else vqa as int);
      assert iOld == (if num.negative then -(vn as int) else vn as int);
      PureArith.SignCastMul(iNew, iOld, vqa, vg, vn, num.negative);
    }
  }

  // Re-exposes Make's value postcondition. Trivial (it IS Make's ensures), but
  // stated as a small standalone lemma so callers need not re-unfold RatValue
  // against Make inside their own heavy contexts.
  lemma MakeValue(num: BigInt.Int, den: seq<limb>, res: Rat)
    requires BigInt.Wf(num) && Normalized(den) && Value(den) > 0
    requires res == Make(num, den)
    ensures Wf(res)
    ensures RatValue(res) == (BigInt.IntValue(num) as real) / (Value(den) as real)
  {}

  //////////////////////////////////////////////////////////////////////////////
  // Arithmetic. Each follows the usual fraction identity and reduces via Make.
  //////////////////////////////////////////////////////////////////////////////

  // A positive denominator as a nonnegative BigInt, for cross-multiplication.
  function FromDen(den: seq<limb>): (r: BigInt.Int)
    requires Normalized(den)
    ensures BigInt.Wf(r)
    ensures BigInt.IntValue(r) == Value(den) as int
    ensures r.mag == den
  {
    BigInt.FromMagnitude(den)
  }

  // x * y = (a*c) / (b*d).
  function Mul(x: Rat, y: Rat): (res: Rat)
    requires Wf(x) && Wf(y)
    ensures Wf(res)
    ensures RatValue(res) == RatValue(x) * RatValue(y)
  {
    var numProd := BigInt.Mul(x.num, y.num);
    var denProd := BigNatMul.Mul(x.den, y.den);
    DenProdPositive(x.den, y.den, denProd);
    var res := Make(numProd, denProd);
    MulValueBridge(x, y, numProd, denProd, res);
    res
  }

  // Bridge RatValue(res) == RatValue(x)*RatValue(y), in its own (small) context.
  @IsolateAssertions
  lemma MulValueBridge(x: Rat, y: Rat, numProd: BigInt.Int, denProd: seq<limb>, res: Rat)
    requires Wf(x) && Wf(y) && BigInt.Wf(numProd) && Normalized(denProd)
    requires BigInt.IntValue(numProd) == BigInt.IntValue(x.num) * BigInt.IntValue(y.num)
    requires Value(denProd) == Value(x.den) * Value(y.den) && Value(denProd) > 0
    requires res == Make(numProd, denProd)
    ensures Wf(res)
    ensures RatValue(res) == RatValue(x) * RatValue(y)
  {
    // Make's ensures already gives RatValue(res) == IntValue(numProd)/Value(denProd);
    // MakeValue re-exposes it in a tiny context so this heavy lemma need not
    // re-unfold RatValue against Make.
    var npR := BigInt.IntValue(numProd) as real;
    var dpR := Value(denProd) as real;
    MakeValue(numProd, denProd, res);
    assert RatValue(res) == npR / dpR;
    MulValueStep(BigInt.IntValue(x.num) as real, Value(x.den) as real,
                 BigInt.IntValue(y.num) as real, Value(y.den) as real,
                 npR, dpR,
                 BigInt.IntValue(numProd), BigInt.IntValue(x.num), BigInt.IntValue(y.num),
                 Value(denProd), Value(x.den), Value(y.den));
  }

  // x + y = (a*d + c*b) / (b*d).
  function Add(x: Rat, y: Rat): (res: Rat)
    requires Wf(x) && Wf(y)
    ensures Wf(res)
    ensures RatValue(res) == RatValue(x) + RatValue(y)
  {
    var ad := BigInt.Mul(x.num, FromDen(y.den));
    var cb := BigInt.Mul(y.num, FromDen(x.den));
    var num := BigInt.Add(ad, cb);
    var den := BigNatMul.Mul(x.den, y.den);
    DenProdPositive(x.den, y.den, den);
    var res := Make(num, den);
    AddValueBridge(x, y, ad, cb, num, den, res);
    res
  }

  @IsolateAssertions
  lemma AddValueBridge(x: Rat, y: Rat, ad: BigInt.Int, cb: BigInt.Int,
                       num: BigInt.Int, den: seq<limb>, res: Rat)
    requires Wf(x) && Wf(y) && BigInt.Wf(num) && Normalized(den)
    requires BigInt.IntValue(ad) == BigInt.IntValue(x.num) * (Value(y.den) as int)
    requires BigInt.IntValue(cb) == BigInt.IntValue(y.num) * (Value(x.den) as int)
    requires BigInt.IntValue(num) == BigInt.IntValue(ad) + BigInt.IntValue(cb)
    requires Value(den) == Value(x.den) * Value(y.den) && Value(den) > 0
    requires res == Make(num, den)
    ensures Wf(res)
    ensures RatValue(res) == RatValue(x) + RatValue(y)
  {
    var nR := BigInt.IntValue(num) as real;
    var dR := Value(den) as real;
    MakeValue(num, den, res);
    assert RatValue(res) == nR / dR;
    AddValueStep(BigInt.IntValue(x.num) as real, Value(x.den) as real,
                 BigInt.IntValue(y.num) as real, Value(y.den) as real,
                 nR, dR,
                 BigInt.IntValue(ad), BigInt.IntValue(cb), BigInt.IntValue(num),
                 BigInt.IntValue(x.num), BigInt.IntValue(y.num),
                 Value(den), Value(x.den), Value(y.den));
  }

  // x - y = x + (-y), reusing Add with a negated numerator.
  function Sub(x: Rat, y: Rat): (res: Rat)
    requires Wf(x) && Wf(y)
    ensures Wf(res)
    ensures RatValue(res) == RatValue(x) - RatValue(y)
  {
    var negY := Rat(BigInt.Negate(y.num), y.den);
    NegRatValue(y, negY);
    Add(x, negY)
  }

  // Compare x and y by cross-multiplication (both denominators positive).
  function Compare(x: Rat, y: Rat): (c: int)
    requires Wf(x) && Wf(y)
    ensures c == 0 <==> RatValue(x) == RatValue(y)
    ensures c < 0 <==> RatValue(x) < RatValue(y)
    ensures c > 0 <==> RatValue(x) > RatValue(y)
  {
    var ad := BigInt.Mul(x.num, FromDen(y.den));
    var cb := BigInt.Mul(y.num, FromDen(x.den));
    var c := BigInt.Compare(ad, cb);
    CompareValueBridge(x, y, ad, cb, c);
    c
  }

  @IsolateAssertions
  lemma CompareValueBridge(x: Rat, y: Rat, ad: BigInt.Int, cb: BigInt.Int, c: int)
    requires Wf(x) && Wf(y)
    requires BigInt.IntValue(ad) == BigInt.IntValue(x.num) * (Value(y.den) as int)
    requires BigInt.IntValue(cb) == BigInt.IntValue(y.num) * (Value(x.den) as int)
    requires c == 0 <==> BigInt.IntValue(ad) == BigInt.IntValue(cb)
    requires c < 0 <==> BigInt.IntValue(ad) < BigInt.IntValue(cb)
    requires c > 0 <==> BigInt.IntValue(ad) > BigInt.IntValue(cb)
    ensures c == 0 <==> RatValue(x) == RatValue(y)
    ensures c < 0 <==> RatValue(x) < RatValue(y)
    ensures c > 0 <==> RatValue(x) > RatValue(y)
  {
    CompareValueStep(BigInt.IntValue(x.num) as real, Value(x.den) as real,
                     BigInt.IntValue(y.num) as real, Value(y.den) as real,
                     c, BigInt.IntValue(ad), BigInt.IntValue(cb),
                     BigInt.IntValue(x.num), BigInt.IntValue(y.num),
                     Value(x.den), Value(y.den));
  }

  //////////////////////////////////////////////////////////////////////////////
  // Value-level proof obligations for the arithmetic, kept out of the function
  // bodies so the recursive IntValue/Value unfolding stays in a small context.
  //////////////////////////////////////////////////////////////////////////////

  lemma DenProdPositive(a: seq<limb>, b: seq<limb>, p: seq<limb>)
    requires Normalized(a) && Normalized(b) && Value(a) > 0 && Value(b) > 0
    requires Value(p) == Value(a) * Value(b) && Normalized(p)
    ensures Value(p) > 0
  {
    PureArith.MulPosPos(Value(a), Value(b), Value(p));
  }

  // Value of -y as a rational.
  lemma NegRatValue(y: Rat, negY: Rat)
    requires Wf(y)
    requires negY == Rat(BigInt.Negate(y.num), y.den)
    ensures Wf(negY)
    ensures RatValue(negY) == -RatValue(y)
  {
    var vy := Value(y.den) as real;
    assert BigInt.IntValue(negY.num) == -BigInt.IntValue(y.num);
    PureArith.NegFrac(BigInt.IntValue(y.num) as real, vy);
  }

  // Value-free: proves (np as real)/(dp as real) == (a/b)*(c/d), given the
  // integer/nat product facts. a,b,c,d are the reals of x.num, x.den, y.num,
  // y.den; npR,dpR the reals of the product numerator/denominator.
  lemma MulValueStep(a: real, b: real, c: real, d: real, npR: real, dpR: real,
                     np: int, na: int, nc: int, dp: nat, db: nat, dd: nat)
    requires b > 0.0 && d > 0.0
    requires a == na as real && b == db as real && c == nc as real && d == dd as real
    requires npR == np as real && dpR == dp as real
    requires np == na * nc && dp == db * dd
    ensures npR / dpR == (a / b) * (c / d)
  {
    PureArith.CastProdInt(np, na, nc);     // npR == a*c
    PureArith.CastProd(dp, db, dd);        // dpR == b*d
    PureArith.RealMulFrac(a, b, c, d);     // (a/b)*(c/d) == (a*c)/(b*d)
  }

  // Value-free: (nR/dR) == a/b + c/d, given the cross products adI == na*dd (= a*d),
  // cbI == nc*db (= c*b), nn == adI+cbI, dp == db*dd (= b*d).
  lemma AddValueStep(a: real, b: real, c: real, d: real, nR: real, dR: real,
                     adI: int, cbI: int, nn: int, na: int, nc: int,
                     dp: nat, db: nat, dd: nat)
    requires b > 0.0 && d > 0.0
    requires a == na as real && b == db as real && c == nc as real && d == dd as real
    requires nR == nn as real && dR == dp as real
    requires adI == na * (dd as int) && cbI == nc * (db as int)
    requires nn == adI + cbI && dp == db * dd
    ensures nR / dR == a / b + c / d
  {
    PureArith.CastProdIntNat(adI, na, dd);   // adI as real == a*d
    PureArith.CastProdIntNat(cbI, nc, db);   // cbI as real == c*b
    PureArith.CastProd(dp, db, dd);          // dR == b*d
    PureArith.RealAddFrac(a, b, c, d);       // a/b + c/d == (a*d + c*b)/(b*d)
  }

  // Value-free: the sign of BigInt.Compare(ad, cb) decides the order of the two
  // fractions, given ad == na*dd (= a*d), cb == nc*db (= c*b), b,d > 0.
  lemma CompareValueStep(a: real, b: real, cc: real, d: real, c: int,
                         adI: int, cbI: int, na: int, nc: int, db: nat, dd: nat)
    requires b > 0.0 && d > 0.0
    requires a == na as real && b == db as real && cc == nc as real && d == dd as real
    requires adI == na * (dd as int) && cbI == nc * (db as int)
    requires c == 0 <==> adI == cbI
    requires c < 0 <==> adI < cbI
    requires c > 0 <==> adI > cbI
    ensures c == 0 <==> a / b == cc / d
    ensures c < 0 <==> a / b < cc / d
    ensures c > 0 <==> a / b > cc / d
  {
    PureArith.CastProdIntNat(adI, na, dd);   // adI as real == a*d
    PureArith.CastProdIntNat(cbI, nc, db);   // cbI as real == cc*b
    PureArith.RealCompareFrac(a, b, cc, d);  // a/b <cmp> cc/d <==> a*d <cmp> cc*b
  }
}

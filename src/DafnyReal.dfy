/*******************************************************************************
 * dafny-bignum: DafnyReal
 *
 * An UNREDUCED rational: a signed BigInt numerator over a strictly positive
 * signed BigInt denominator, never reduced to lowest terms. This models Dafny's
 * built-in `real` (and the C++ backend's DafnyReal / C#'s Dafny.BigRational),
 * where the denominator is significant: it decides how many decimal places
 * `print` shows. 1.5*1.0 is 150/100 and must print "1.50", so reducing to 3/2
 * would be wrong. Hence — unlike Rational.dfy — there is NO automatic gcd here.
 *
 * Reduction exists only as an explicit opt-in (`Reduce`). add / sub / mul /
 * compare keep the raw cross-denominator, matching the backend semantics.
 *
 * Specified against RealValue(): the real number num/den.
 *******************************************************************************/

include "BigNat.dfy"
include "BigInt.dfy"
include "BigNatGCD.dfy"
include "BigNatDivMod.dfy"
include "PureArith.dfy"

module DafnyReal {
  import opened BigNat
  import BigInt
  import BigNatGCD
  import BigNatDivMod
  import PureArith

  // num / den with den > 0. Unreduced on purpose. The sign lives in num.
  datatype DReal = DReal(num: BigInt.Int, den: BigInt.Int)

  predicate Wf(x: DReal)
  {
    BigInt.Wf(x.num) && BigInt.Wf(x.den) && BigInt.IntValue(x.den) > 0
  }

  // The real number denoted. den > 0 (from Wf), so the division is defined.
  function RealValue(x: DReal): real
    requires Wf(x)
  {
    BigInt.IntValue(x.num) as real / BigInt.IntValue(x.den) as real
  }

  // Build from a numerator and a positive denominator, WITHOUT reducing.
  function Make(num: BigInt.Int, den: BigInt.Int): (r: DReal)
    requires BigInt.Wf(num) && BigInt.Wf(den) && BigInt.IntValue(den) > 0
    ensures Wf(r)
    ensures RealValue(r) == BigInt.IntValue(num) as real / BigInt.IntValue(den) as real
  {
    DReal(num, den)
  }

  // A whole number n as n/1.
  function FromInt(n: BigInt.Int): (r: DReal)
    requires BigInt.Wf(n)
    ensures Wf(r)
    ensures RealValue(r) == BigInt.IntValue(n) as real
  {
    var one := BigInt.FromMagnitude(BigNat.One);
    OneIsOne(one);
    DReal(n, one)
  }

  lemma OneIsOne(one: BigInt.Int)
    requires one == BigInt.FromMagnitude(BigNat.One)
    ensures BigInt.Wf(one) && BigInt.IntValue(one) == 1
  {
    ValueOne();
  }

  //////////////////////////////////////////////////////////////////////////////
  // Arithmetic — keeps the raw cross-denominator (no reduction).
  //////////////////////////////////////////////////////////////////////////////

  // a/b + c/d == (a*d + c*b)/(b*d), denominator b*d kept unreduced.
  function Add(x: DReal, y: DReal): (r: DReal)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) + RealValue(y)
  {
    var ad := BigInt.Mul(x.num, y.den);
    var cb := BigInt.Mul(y.num, x.den);
    var num := BigInt.Add(ad, cb);
    var den := BigInt.Mul(x.den, y.den);
    DenPositive(x.den, y.den, den);
    AddValueBridge(x, y, ad, cb, num, den);
    DReal(num, den)
  }

  // a/b - c/d == (a*d - c*b)/(b*d).
  function Sub(x: DReal, y: DReal): (r: DReal)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) - RealValue(y)
  {
    var ad := BigInt.Mul(x.num, y.den);
    var cb := BigInt.Mul(y.num, x.den);
    var num := BigInt.Sub(ad, cb);
    var den := BigInt.Mul(x.den, y.den);
    DenPositive(x.den, y.den, den);
    SubValueBridge(x, y, ad, cb, num, den);
    DReal(num, den)
  }

  // (a/b)*(c/d) == (a*c)/(b*d).
  function Mul(x: DReal, y: DReal): (r: DReal)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) * RealValue(y)
  {
    var num := BigInt.Mul(x.num, y.num);
    var den := BigInt.Mul(x.den, y.den);
    DenPositive(x.den, y.den, den);
    MulValueBridge(x, y, num, den);
    DReal(num, den)
  }

  // Compare by sign of (a*d - c*b); denominators are positive.
  function Compare(x: DReal, y: DReal): (c: int)
    requires Wf(x) && Wf(y)
    ensures c == 0 <==> RealValue(x) == RealValue(y)
    ensures c < 0 <==> RealValue(x) < RealValue(y)
    ensures c > 0 <==> RealValue(x) > RealValue(y)
  {
    var ad := BigInt.Mul(x.num, y.den);
    var cb := BigInt.Mul(y.num, x.den);
    CompareValueBridge(x, y, ad, cb);
    BigInt.Compare(ad, cb)
  }

  //////////////////////////////////////////////////////////////////////////////
  // The denominator b*d of two positive dens is positive.
  //////////////////////////////////////////////////////////////////////////////

  lemma DenPositive(b: BigInt.Int, d: BigInt.Int, prod: BigInt.Int)
    requires BigInt.Wf(b) && BigInt.Wf(d) && BigInt.Wf(prod)
    requires BigInt.IntValue(b) > 0 && BigInt.IntValue(d) > 0
    requires BigInt.IntValue(prod) == BigInt.IntValue(b) * BigInt.IntValue(d)
    ensures BigInt.IntValue(prod) > 0
  {
    PureArith.MulPosPosInt(BigInt.IntValue(b), BigInt.IntValue(d));
  }

  //////////////////////////////////////////////////////////////////////////////
  // Value bridges: each binds IntValue() to plain ints up front and hands the
  // nonlinear real-fraction algebra to PureArith, so Z3 never forms a product of
  // recursive IntValue() terms in a heavy context.
  //////////////////////////////////////////////////////////////////////////////

  @IsolateAssertions
  lemma AddValueBridge(x: DReal, y: DReal, ad: BigInt.Int, cb: BigInt.Int,
                       num: BigInt.Int, den: BigInt.Int)
    requires Wf(x) && Wf(y)
    requires BigInt.IntValue(ad) == BigInt.IntValue(x.num) * BigInt.IntValue(y.den)
    requires BigInt.IntValue(cb) == BigInt.IntValue(y.num) * BigInt.IntValue(x.den)
    requires BigInt.IntValue(num) == BigInt.IntValue(ad) + BigInt.IntValue(cb)
    requires BigInt.IntValue(den) == BigInt.IntValue(x.den) * BigInt.IntValue(y.den)
    requires BigInt.IntValue(den) > 0
    ensures (BigInt.IntValue(num) as real) / (BigInt.IntValue(den) as real)
            == (BigInt.IntValue(x.num) as real / BigInt.IntValue(x.den) as real)
             + (BigInt.IntValue(y.num) as real / BigInt.IntValue(y.den) as real)
  {
    var a := BigInt.IntValue(x.num); var b := BigInt.IntValue(x.den);
    var c := BigInt.IntValue(y.num); var d := BigInt.IntValue(y.den);
    var adv := BigInt.IntValue(ad); var cbv := BigInt.IntValue(cb);
    var nv := BigInt.IntValue(num); var dv := BigInt.IntValue(den);
    // real casts of the integer products
    PureArith.CastProdInt(adv, a, d);
    PureArith.CastProdInt(cbv, c, b);
    PureArith.CastProdInt(dv, b, d);
    // b, d != 0 as reals
    assert (b as real) != 0.0 && (d as real) != 0.0;
    PureArith.RealAddFrac(a as real, b as real, c as real, d as real);
  }

  @IsolateAssertions
  lemma SubValueBridge(x: DReal, y: DReal, ad: BigInt.Int, cb: BigInt.Int,
                       num: BigInt.Int, den: BigInt.Int)
    requires Wf(x) && Wf(y)
    requires BigInt.IntValue(ad) == BigInt.IntValue(x.num) * BigInt.IntValue(y.den)
    requires BigInt.IntValue(cb) == BigInt.IntValue(y.num) * BigInt.IntValue(x.den)
    requires BigInt.IntValue(num) == BigInt.IntValue(ad) - BigInt.IntValue(cb)
    requires BigInt.IntValue(den) == BigInt.IntValue(x.den) * BigInt.IntValue(y.den)
    requires BigInt.IntValue(den) > 0
    ensures (BigInt.IntValue(num) as real) / (BigInt.IntValue(den) as real)
            == (BigInt.IntValue(x.num) as real / BigInt.IntValue(x.den) as real)
             - (BigInt.IntValue(y.num) as real / BigInt.IntValue(y.den) as real)
  {
    var a := BigInt.IntValue(x.num); var b := BigInt.IntValue(x.den);
    var c := BigInt.IntValue(y.num); var d := BigInt.IntValue(y.den);
    PureArith.CastProdInt(BigInt.IntValue(ad), a, d);
    PureArith.CastProdInt(BigInt.IntValue(cb), c, b);
    PureArith.CastProdInt(BigInt.IntValue(den), b, d);
    assert (b as real) != 0.0 && (d as real) != 0.0;
    PureArith.RealSubFrac(a as real, b as real, c as real, d as real);
  }

  @IsolateAssertions
  lemma MulValueBridge(x: DReal, y: DReal, num: BigInt.Int, den: BigInt.Int)
    requires Wf(x) && Wf(y)
    requires BigInt.IntValue(num) == BigInt.IntValue(x.num) * BigInt.IntValue(y.num)
    requires BigInt.IntValue(den) == BigInt.IntValue(x.den) * BigInt.IntValue(y.den)
    requires BigInt.IntValue(den) > 0
    ensures (BigInt.IntValue(num) as real) / (BigInt.IntValue(den) as real)
            == (BigInt.IntValue(x.num) as real / BigInt.IntValue(x.den) as real)
             * (BigInt.IntValue(y.num) as real / BigInt.IntValue(y.den) as real)
  {
    var a := BigInt.IntValue(x.num); var b := BigInt.IntValue(x.den);
    var c := BigInt.IntValue(y.num); var d := BigInt.IntValue(y.den);
    PureArith.CastProdInt(BigInt.IntValue(num), a, c);
    PureArith.CastProdInt(BigInt.IntValue(den), b, d);
    assert (b as real) != 0.0 && (d as real) != 0.0;
    PureArith.RealMulFrac(a as real, b as real, c as real, d as real);
  }

  @IsolateAssertions
  lemma CompareValueBridge(x: DReal, y: DReal, ad: BigInt.Int, cb: BigInt.Int)
    requires Wf(x) && Wf(y)
    requires BigInt.IntValue(ad) == BigInt.IntValue(x.num) * BigInt.IntValue(y.den)
    requires BigInt.IntValue(cb) == BigInt.IntValue(y.num) * BigInt.IntValue(x.den)
    ensures (BigInt.IntValue(ad) < BigInt.IntValue(cb)) <==> (RealValue(x) < RealValue(y))
    ensures (BigInt.IntValue(ad) == BigInt.IntValue(cb)) <==> (RealValue(x) == RealValue(y))
    ensures (BigInt.IntValue(ad) > BigInt.IntValue(cb)) <==> (RealValue(x) > RealValue(y))
  {
    var a := BigInt.IntValue(x.num); var b := BigInt.IntValue(x.den);
    var c := BigInt.IntValue(y.num); var d := BigInt.IntValue(y.den);
    PureArith.CastProdInt(BigInt.IntValue(ad), a, d);
    PureArith.CastProdInt(BigInt.IntValue(cb), c, b);
    assert (b as real) > 0.0 && (d as real) > 0.0;
    PureArith.RealCompareFrac(a as real, b as real, c as real, d as real);
  }
}

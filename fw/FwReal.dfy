/*******************************************************************************
 * dafny-bignum / fixed-width: FwReal
 *
 * An UNREDUCED num/den rational on top of the fixed-width signed FwInt, modelling
 * Dafny's runtime BigRational (its `real`). The denominator is kept UNREDUCED on
 * purpose: it carries how many decimal places `print` shows (1.5*1.0 is 150/100
 * and must print "1.50", not "1.5"). So there is deliberately NO gcd / reduction.
 *
 * Same fixed-width rule as the rest of fw/: every executable value is a native
 * type (FwInt.Int / bool / cmp / seq), int/nat only in ghost specs, so the
 * generated code is Boost-free.
 *
 *   Real(num, den)   den > 0 (Wf).  RealValue = IntValue(num) / IntValue(den).
 *
 * Add/Sub use the raw cross-denominator b*d (no common-denominator reduction).
 * Mul/Div are raw cross products. Compare is sign-of-(a*d - c*b) via FwInt.
 *******************************************************************************/

include "FwNat.dfy"
include "FwInt.dfy"
include "FwCompare.dfy"
include "FwRealArith.dfy"

module FwReal {
  import FwInt
  import opened FwCompare
  import FwRealArith

  // num / den with den > 0. Unreduced on purpose. Sign lives in num.
  datatype Real = Real(num: FwInt.Int, den: FwInt.Int)

  ghost predicate Wf(x: Real)
  {
    FwInt.Wf(x.num) && FwInt.Wf(x.den) && FwInt.IntValue(x.den) > 0
  }

  ghost function RealValue(x: Real): real
    requires Wf(x)
  {
    FwInt.IntValue(x.num) as real / FwInt.IntValue(x.den) as real
  }

  //////////////////////////////////////////////////////////////////////////////
  // Positive-denominator helper: product of two positive FwInt dens is positive.
  //////////////////////////////////////////////////////////////////////////////

  lemma DenPositive(b: FwInt.Int, d: FwInt.Int, prod: FwInt.Int)
    requires FwInt.IntValue(b) > 0 && FwInt.IntValue(d) > 0
    requires FwInt.IntValue(prod) == FwInt.IntValue(b) * FwInt.IntValue(d)
    ensures FwInt.IntValue(prod) > 0
  {
    FwRealArith.MulPosPosInt(FwInt.IntValue(b), FwInt.IntValue(d));
  }

  //////////////////////////////////////////////////////////////////////////////
  // Constructors.
  //////////////////////////////////////////////////////////////////////////////

  // Build num/den with den > 0, WITHOUT reducing.
  method Make(num: FwInt.Int, den: FwInt.Int) returns (r: Real)
    requires FwInt.Wf(num) && FwInt.Wf(den) && FwInt.IntValue(den) > 0
    ensures Wf(r)
    ensures RealValue(r) == FwInt.IntValue(num) as real / FwInt.IntValue(den) as real
  {
    r := Real(num, den);
  }

  // A whole number n as n/1.
  method FromInt(n: FwInt.Int) returns (r: Real)
    requires FwInt.Wf(n)
    ensures Wf(r)
    ensures RealValue(r) == FwInt.IntValue(n) as real
  {
    var one := FwInt.FromMagnitude([1]);     // Value([1]) == 1
    assert FwInt.IntValue(one) == 1;
    r := Real(n, one);
    assert RealValue(r) == FwInt.IntValue(n) as real / 1.0;
  }

  //////////////////////////////////////////////////////////////////////////////
  // Addition / subtraction over the raw cross-denominator b*d (unreduced).
  //////////////////////////////////////////////////////////////////////////////

  method Add(x: Real, y: Real) returns (r: Real)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) + RealValue(y)
  {
    var ad := FwInt.Mul(x.num, y.den);
    var cb := FwInt.Mul(y.num, x.den);
    var num := FwInt.Add(ad, cb);
    var den := FwInt.Mul(x.den, y.den);
    DenPositive(x.den, y.den, den);
    AddValue(x, y, ad, cb, num, den);
    r := Real(num, den);
  }

  lemma AddValue(x: Real, y: Real, ad: FwInt.Int, cb: FwInt.Int,
                 num: FwInt.Int, den: FwInt.Int)
    requires Wf(x) && Wf(y)
    requires FwInt.IntValue(ad) == FwInt.IntValue(x.num) * FwInt.IntValue(y.den)
    requires FwInt.IntValue(cb) == FwInt.IntValue(y.num) * FwInt.IntValue(x.den)
    requires FwInt.IntValue(num) == FwInt.IntValue(ad) + FwInt.IntValue(cb)
    requires FwInt.IntValue(den) == FwInt.IntValue(x.den) * FwInt.IntValue(y.den)
    requires FwInt.IntValue(den) > 0
    ensures (FwInt.IntValue(num) as real) / (FwInt.IntValue(den) as real)
            == (FwInt.IntValue(x.num) as real / FwInt.IntValue(x.den) as real)
             + (FwInt.IntValue(y.num) as real / FwInt.IntValue(y.den) as real)
  {
    // Bind every IntValue to a plain int; the nonlinear algebra is then pure int
    // in FwRealArith, with no recursive bignum function in scope.
    ghost var a := FwInt.IntValue(x.num); ghost var b := FwInt.IntValue(x.den);
    ghost var c := FwInt.IntValue(y.num); ghost var d := FwInt.IntValue(y.den);
    ghost var adv := FwInt.IntValue(ad); ghost var cbv := FwInt.IntValue(cb);
    ghost var numv := FwInt.IntValue(num); ghost var denv := FwInt.IntValue(den);
    FwRealArith.AddFracFromProducts(a, b, c, d, adv, cbv, numv, denv);
  }

  method Sub(x: Real, y: Real) returns (r: Real)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) - RealValue(y)
  {
    var ad := FwInt.Mul(x.num, y.den);
    var cb := FwInt.Mul(y.num, x.den);
    var num := FwInt.Sub(ad, cb);
    var den := FwInt.Mul(x.den, y.den);
    DenPositive(x.den, y.den, den);
    SubValue(x, y, ad, cb, num, den);
    r := Real(num, den);
  }

  lemma SubValue(x: Real, y: Real, ad: FwInt.Int, cb: FwInt.Int,
                 num: FwInt.Int, den: FwInt.Int)
    requires Wf(x) && Wf(y)
    requires FwInt.IntValue(ad) == FwInt.IntValue(x.num) * FwInt.IntValue(y.den)
    requires FwInt.IntValue(cb) == FwInt.IntValue(y.num) * FwInt.IntValue(x.den)
    requires FwInt.IntValue(num) == FwInt.IntValue(ad) - FwInt.IntValue(cb)
    requires FwInt.IntValue(den) == FwInt.IntValue(x.den) * FwInt.IntValue(y.den)
    requires FwInt.IntValue(den) > 0
    ensures (FwInt.IntValue(num) as real) / (FwInt.IntValue(den) as real)
            == (FwInt.IntValue(x.num) as real / FwInt.IntValue(x.den) as real)
             - (FwInt.IntValue(y.num) as real / FwInt.IntValue(y.den) as real)
  {
    ghost var a := FwInt.IntValue(x.num); ghost var b := FwInt.IntValue(x.den);
    ghost var c := FwInt.IntValue(y.num); ghost var d := FwInt.IntValue(y.den);
    ghost var adv := FwInt.IntValue(ad); ghost var cbv := FwInt.IntValue(cb);
    ghost var numv := FwInt.IntValue(num); ghost var denv := FwInt.IntValue(den);
    FwRealArith.SubFracFromProducts(a, b, c, d, adv, cbv, numv, denv);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Negation: (-num)/den.
  //////////////////////////////////////////////////////////////////////////////

  method Neg(x: Real) returns (r: Real)
    requires Wf(x)
    ensures Wf(r)
    ensures RealValue(r) == -RealValue(x)
  {
    var num := FwInt.Negate(x.num);
    NegValue(x, num);
    r := Real(num, x.den);
  }

  lemma NegValue(x: Real, num: FwInt.Int)
    requires Wf(x) && FwInt.Wf(num)
    requires FwInt.IntValue(num) == -FwInt.IntValue(x.num)
    ensures RealValue(Real(num, x.den)) == -RealValue(x)
  {
    FwRealArith.NegFrac(FwInt.IntValue(x.num) as real, FwInt.IntValue(x.den) as real);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Multiplication: (a*c)/(b*d), raw.
  //////////////////////////////////////////////////////////////////////////////

  method Mul(x: Real, y: Real) returns (r: Real)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) * RealValue(y)
  {
    var num := FwInt.Mul(x.num, y.num);
    var den := FwInt.Mul(x.den, y.den);
    DenPositive(x.den, y.den, den);
    MulValue(x, y, num, den);
    r := Real(num, den);
  }

  lemma MulValue(x: Real, y: Real, num: FwInt.Int, den: FwInt.Int)
    requires Wf(x) && Wf(y)
    requires FwInt.IntValue(num) == FwInt.IntValue(x.num) * FwInt.IntValue(y.num)
    requires FwInt.IntValue(den) == FwInt.IntValue(x.den) * FwInt.IntValue(y.den)
    requires FwInt.IntValue(den) > 0
    ensures (FwInt.IntValue(num) as real) / (FwInt.IntValue(den) as real)
            == (FwInt.IntValue(x.num) as real / FwInt.IntValue(x.den) as real)
             * (FwInt.IntValue(y.num) as real / FwInt.IntValue(y.den) as real)
  {
    ghost var a := FwInt.IntValue(x.num); ghost var b := FwInt.IntValue(x.den);
    ghost var c := FwInt.IntValue(y.num); ghost var d := FwInt.IntValue(y.den);
    ghost var numv := FwInt.IntValue(num); ghost var denv := FwInt.IntValue(den);
    FwRealArith.MulFracFromProducts(a, b, c, d, numv, denv);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Division: multiply by the reciprocal of y. Requires y != 0.
  //////////////////////////////////////////////////////////////////////////////

  // Reciprocal of y as a Wf Real (positive denominator), requires y.num != 0.
  method Reciprocal(y: Real) returns (r: Real)
    requires Wf(y) && FwInt.IntValue(y.num) != 0
    ensures Wf(r)
    ensures RealValue(r) == 1.0 / RealValue(y)
  {
    // Nonzero num: its sign is exactly y.num.negative (Wf: zero ==> !negative,
    // and nonzero magnitude is strictly positive).
    NumSignFromNegative(y.num);
    if !y.num.negative {
      // y.num > 0: reciprocal is den/num, both positive.
      ReciprocalValue(y, y.den, y.num);
      r := Real(y.den, y.num);
    } else {
      // y.num < 0: reciprocal is (-den)/(-num), denominator -num > 0.
      var rnum := FwInt.Negate(y.den);
      var rden := FwInt.Negate(y.num);
      ReciprocalValueNeg(y, rnum, rden);
      r := Real(rnum, rden);
    }
  }

  // For a well-formed nonzero FwInt, the sign flag decides the sign of IntValue.
  lemma NumSignFromNegative(n: FwInt.Int)
    requires FwInt.Wf(n) && FwInt.IntValue(n) != 0
    ensures !n.negative ==> FwInt.IntValue(n) > 0
    ensures n.negative ==> FwInt.IntValue(n) < 0
  {
    // IntValue(n) != 0 forces n.mag != [], and a normalized nonempty magnitude
    // has Value > 0, so the sign flag determines the sign.
    if n.mag != [] {
      FwInt.NonEmptyMagPositive(n.mag);
    }
  }

  lemma ReciprocalValue(y: Real, rnum: FwInt.Int, rden: FwInt.Int)
    requires Wf(y) && FwInt.IntValue(y.num) > 0
    requires rnum == y.den && rden == y.num
    ensures FwInt.IntValue(rden) > 0
    ensures (FwInt.IntValue(rnum) as real) / (FwInt.IntValue(rden) as real) == 1.0 / RealValue(y)
  {
    FwRealArith.ReciprocalFrac(FwInt.IntValue(y.num) as real, FwInt.IntValue(y.den) as real);
  }

  lemma ReciprocalValueNeg(y: Real, rnum: FwInt.Int, rden: FwInt.Int)
    requires Wf(y) && FwInt.IntValue(y.num) < 0
    requires FwInt.IntValue(rnum) == -FwInt.IntValue(y.den)
    requires FwInt.IntValue(rden) == -FwInt.IntValue(y.num)
    ensures FwInt.IntValue(rden) > 0
    ensures (FwInt.IntValue(rnum) as real) / (FwInt.IntValue(rden) as real) == 1.0 / RealValue(y)
  {
    FwRealArith.ReciprocalFracNeg(FwInt.IntValue(y.num) as real, FwInt.IntValue(y.den) as real);
  }

  method Div(x: Real, y: Real) returns (r: Real)
    requires Wf(x) && Wf(y) && FwInt.IntValue(y.num) != 0
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) / RealValue(y)
  {
    var recip := Reciprocal(y);
    r := Mul(x, recip);
    DivValue(x, y, recip, r);
  }

  lemma DivValue(x: Real, y: Real, recip: Real, r: Real)
    requires Wf(x) && Wf(y) && Wf(recip) && Wf(r)
    requires FwInt.IntValue(y.num) != 0
    requires RealValue(recip) == 1.0 / RealValue(y)
    requires RealValue(r) == RealValue(x) * RealValue(recip)
    ensures RealValue(r) == RealValue(x) / RealValue(y)
  {
    assert (FwInt.IntValue(y.num) as real) != 0.0;
    assert RealValue(y) != 0.0;
    FwRealArith.DivIsMulRecip(RealValue(x), RealValue(y));
  }

  //////////////////////////////////////////////////////////////////////////////
  // Comparison: sign of (a*d - c*b), denominators positive.
  //////////////////////////////////////////////////////////////////////////////

  method Compare(x: Real, y: Real) returns (c: cmp)
    requires Wf(x) && Wf(y)
    ensures c == 0 <==> RealValue(x) == RealValue(y)
    ensures c < 0 <==> RealValue(x) < RealValue(y)
    ensures c > 0 <==> RealValue(x) > RealValue(y)
  {
    var ad := FwInt.Mul(x.num, y.den);
    var cb := FwInt.Mul(y.num, x.den);
    c := FwInt.Compare(ad, cb);
    CompareValue(x, y, ad, cb);
  }

  lemma CompareValue(x: Real, y: Real, ad: FwInt.Int, cb: FwInt.Int)
    requires Wf(x) && Wf(y)
    requires FwInt.IntValue(ad) == FwInt.IntValue(x.num) * FwInt.IntValue(y.den)
    requires FwInt.IntValue(cb) == FwInt.IntValue(y.num) * FwInt.IntValue(x.den)
    ensures (FwInt.IntValue(ad) < FwInt.IntValue(cb)) <==> (RealValue(x) < RealValue(y))
    ensures (FwInt.IntValue(ad) == FwInt.IntValue(cb)) <==> (RealValue(x) == RealValue(y))
    ensures (FwInt.IntValue(ad) > FwInt.IntValue(cb)) <==> (RealValue(x) > RealValue(y))
  {
    ghost var a := FwInt.IntValue(x.num); ghost var b := FwInt.IntValue(x.den);
    ghost var c := FwInt.IntValue(y.num); ghost var d := FwInt.IntValue(y.den);
    ghost var adv := FwInt.IntValue(ad); ghost var cbv := FwInt.IntValue(cb);
    FwRealArith.CompareFracFromProducts(a, b, c, d, adv, cbv);
  }
}

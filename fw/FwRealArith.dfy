/*******************************************************************************
 * dafny-bignum / fixed-width: FwRealArith
 *
 * Pure real- and int-arithmetic helper lemmas for FwReal, with NO dependency on
 * the fixed-width BigNat layer. Keeping these in a module that never sees
 * Value/FwInt means the SMT solver has none of the recursive bignum axioms in
 * scope, so the nonlinear real/int facts verify stably. (Mirror of the real
 * fraction lemmas in src/PureArith.dfy.)
 *
 * These are all ghost lemmas — nothing compiled — so there is no Boost concern.
 *******************************************************************************/

module FwRealArith {

  // Sum of two fractions over the raw cross-denominator b*d.
  lemma RealAddFrac(a: real, b: real, c: real, d: real)
    requires b != 0.0 && d != 0.0
    ensures a / b + c / d == (a * d + c * b) / (b * d)
  {
    calc {
      a / b + c / d;
      == (a * d) / (b * d) + (c * b) / (d * b);
      == { assert d * b == b * d; }
      (a * d) / (b * d) + (c * b) / (b * d);
      == (a * d + c * b) / (b * d);
    }
  }

  // Difference of two fractions over the raw cross-denominator b*d.
  lemma RealSubFrac(a: real, b: real, c: real, d: real)
    requires b != 0.0 && d != 0.0
    ensures a / b - c / d == (a * d - c * b) / (b * d)
  {
    calc {
      a / b - c / d;
      == (a * d) / (b * d) - (c * b) / (d * b);
      == { assert d * b == b * d; }
      (a * d) / (b * d) - (c * b) / (b * d);
      == (a * d - c * b) / (b * d);
    }
  }

  // Product of two fractions.
  lemma RealMulFrac(a: real, b: real, c: real, d: real)
    requires b != 0.0 && d != 0.0
    ensures (a / b) * (c / d) == (a * c) / (b * d)
  {}

  // Sign of (a*d - c*b) decides the order of a/b and c/d when b,d > 0.
  lemma RealCompareFrac(a: real, b: real, c: real, d: real)
    requires b > 0.0 && d > 0.0
    ensures a / b < c / d <==> a * d < c * b
    ensures a / b == c / d <==> a * d == c * b
    ensures a / b > c / d <==> a * d > c * b
  {}

  // p == a*b (ints) ==> (p as real) == (a as real)*(b as real).
  lemma CastProdInt(p: int, a: int, b: int)
    requires p == a * b
    ensures (p as real) == (a as real) * (b as real)
  {}

  // Product of two positive ints is positive.
  lemma MulPosPosInt(a: int, b: int)
    requires a > 0 && b > 0
    ensures a * b > 0
  {}

  // Negating the numerator negates the fraction.
  lemma NegFrac(a: real, b: real)
    requires b != 0.0
    ensures (-a) / b == -(a / b)
  {}

  // Reciprocal of a positive-numerator fraction.
  lemma ReciprocalFrac(num: real, den: real)
    requires num > 0.0 && den > 0.0
    ensures den / num == 1.0 / (num / den)
  {}

  // Reciprocal when num < 0: (-den)/(-num) == 1/(num/den). den > 0, num < 0.
  lemma ReciprocalFracNeg(num: real, den: real)
    requires num < 0.0 && den > 0.0
    ensures (-den) / (-num) == 1.0 / (num / den)
  {}

  // Division as multiplication by the reciprocal.
  lemma DivIsMulRecip(x: real, y: real)
    requires y != 0.0
    ensures x * (1.0 / y) == x / y
  {}

  //////////////////////////////////////////////////////////////////////////////
  // Combined "from integer products" bridges. These take ONLY plain ints, so no
  // recursive bignum function (IntValue/Value) is ever in scope here — which is
  // what keeps the nonlinear reasoning stable. FwReal binds its IntValues to
  // locals and calls these.
  //////////////////////////////////////////////////////////////////////////////

  // adv == a*d, cbv == c*b, numv == adv+cbv, denv == b*d, b,d != 0  ==>
  //   numv/denv == a/b + c/d  (as reals).
  lemma AddFracFromProducts(a: int, b: int, c: int, d: int,
                            adv: int, cbv: int, numv: int, denv: int)
    requires b != 0 && d != 0
    requires adv == a * d && cbv == c * b && numv == adv + cbv && denv == b * d
    ensures (numv as real) / (denv as real)
            == (a as real) / (b as real) + (c as real) / (d as real)
  {
    CastProdInt(adv, a, d);
    CastProdInt(cbv, c, b);
    CastProdInt(denv, b, d);
    RealAddFrac(a as real, b as real, c as real, d as real);
  }

  // numv == adv - cbv, else as above ==> numv/denv == a/b - c/d.
  lemma SubFracFromProducts(a: int, b: int, c: int, d: int,
                            adv: int, cbv: int, numv: int, denv: int)
    requires b != 0 && d != 0
    requires adv == a * d && cbv == c * b && numv == adv - cbv && denv == b * d
    ensures (numv as real) / (denv as real)
            == (a as real) / (b as real) - (c as real) / (d as real)
  {
    CastProdInt(adv, a, d);
    CastProdInt(cbv, c, b);
    CastProdInt(denv, b, d);
    RealSubFrac(a as real, b as real, c as real, d as real);
  }

  // numv == a*c, denv == b*d, b,d != 0 ==> numv/denv == (a/b)*(c/d).
  lemma MulFracFromProducts(a: int, b: int, c: int, d: int, numv: int, denv: int)
    requires b != 0 && d != 0
    requires numv == a * c && denv == b * d
    ensures (numv as real) / (denv as real)
            == ((a as real) / (b as real)) * ((c as real) / (d as real))
  {
    CastProdInt(numv, a, c);
    CastProdInt(denv, b, d);
    RealMulFrac(a as real, b as real, c as real, d as real);
  }

  // Compare a/b and c/d (b,d > 0) by the signs of the cross products a*d, c*b.
  lemma CompareFracFromProducts(a: int, b: int, c: int, d: int, adv: int, cbv: int)
    requires b > 0 && d > 0
    requires adv == a * d && cbv == c * b
    ensures (adv < cbv) <==> ((a as real) / (b as real) < (c as real) / (d as real))
    ensures (adv == cbv) <==> ((a as real) / (b as real) == (c as real) / (d as real))
    ensures (adv > cbv) <==> ((a as real) / (b as real) > (c as real) / (d as real))
  {
    CastProdInt(adv, a, d);
    CastProdInt(cbv, c, b);
    RealCompareFrac(a as real, b as real, c as real, d as real);
  }
}

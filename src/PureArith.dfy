/*******************************************************************************
 * dafny-bignum: PureArith
 *
 * Pure real- and nat-arithmetic helper lemmas, with NO dependency on the bignum
 * layer. Keeping these in a module that never sees Value/BigNat means the SMT
 * solver has none of the recursive bignum function axioms in scope, so the
 * nonlinear real/nat products here verify stably (in the full Rational context
 * the same lemmas time out because Z3 drifts into the recursive axioms).
 *******************************************************************************/

module PureArith {

  //////////////////////////////////////////////////////////////////////////////
  // Real fraction identities.
  //////////////////////////////////////////////////////////////////////////////

  // Cancelling a common nonzero factor g from numerator and denominator.
  lemma RealCancel(a: real, b: real, g: real)
    requires b != 0.0 && g != 0.0
    ensures (a * g) / (b * g) == a / b
  {
    calc {
      (a * g) / (b * g);
      == { assert b * g != 0.0; }
      (a / b) * (g / g);
      == { assert g / g == 1.0; }
      a / b;
    }
  }

  // Sum of two fractions over a common cross-denominator.
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

  // Product of two fractions.
  lemma RealMulFrac(a: real, b: real, c: real, d: real)
    requires b != 0.0 && d != 0.0
    ensures (a / b) * (c / d) == (a * c) / (b * d)
  {
  }

  // Sign of (a*d - c*b) decides the order of a/b and c/d when b,d > 0.
  lemma RealCompareFrac(a: real, b: real, c: real, d: real)
    requires b > 0.0 && d > 0.0
    ensures a / b < c / d <==> a * d < c * b
    ensures a / b == c / d <==> a * d == c * b
    ensures a / b > c / d <==> a * d > c * b
  {
    // Z3 discharges this directly (real linear arithmetic with b,d > 0).
  }

  //////////////////////////////////////////////////////////////////////////////
  // Nat division / multiplication facts.
  //////////////////////////////////////////////////////////////////////////////

  lemma MulComm(a: nat, b: nat) ensures a * b == b * a {}

  lemma MulMonoRight(a: nat, b: nat, c: nat)
    requires a <= b
    ensures a * c <= b * c
  {}

  lemma DistribRight(a: nat, b: nat, c: nat)
    ensures (a + b) * c == a * c + b * c
  {}

  lemma MulLowerBound(a: nat, d: nat)
    requires a >= 1 && d > 0
    ensures a * d >= d
  {
    assert a * d >= 1 * d by { MulMonoRight(1, a, d); }
  }

  // q*d + r == k*d with 0 <= r < d forces r == 0, q == k.
  lemma UniqueDivMod(d: nat, q: nat, r: nat, k: nat)
    requires d > 0 && r < d
    requires q * d + r == k * d
    ensures r == 0 && q == k
  {
    if q < k {
      // (k-q)*d == r < d, but k-q >= 1 so (k-q)*d >= d. Contradiction.
      MulLowerBound(k - q, d);
      assert (k - q) * d == r;
    } else if q > k {
      // r == k*d - q*d == -(q-k)*d < 0, impossible for nat r.
      MulLowerBound(q - k, d);
      assert q * d == k * d + r;
      assert (q - k) * d + k * d == q * d by { DistribRight(q - k, k, d); }
    }
  }

  // If d divides n (n == d*k) and DivMod gives n == q*d + r with r < d, then
  // r == 0 and q == k. Pure nat reasoning (division is unique).
  lemma ExactQuotient(n: nat, d: nat, q: nat, r: nat, k: nat)
    requires d > 0
    requires n == q * d + r && r < d
    requires n == d * k
    ensures r == 0 && q == k
  {
    assert d * k == k * d by { MulComm(d, k); }
    assert q * d + r == k * d;
    UniqueDivMod(d, q, r, k);
  }

  // (a*b) as real == (a as real)*(b as real) for nats.
  lemma CastMul(a: nat, b: nat)
    ensures (a * b) as real == (a as real) * (b as real)
  {}

  // If p == a*b (nats), then (p as real) == (a as real)*(b as real). Lets the
  // caller pass the already-formed product p so no nat*nat is built in its scope.
  lemma CastProd(p: nat, a: nat, b: nat)
    requires p == a * b
    ensures (p as real) == (a as real) * (b as real)
  {
    CastMul(a, b);
  }

  // Int version: p == a*b (ints) ==> (p as real) == (a as real)*(b as real).
  lemma CastProdInt(p: int, a: int, b: int)
    requires p == a * b
    ensures (p as real) == (a as real) * (b as real)
  {}

  // Mixed int*nat: p == a * (b as int) ==> real casts multiply.
  lemma CastProdIntNat(p: int, a: int, b: nat)
    requires p == a * (b as int)
    ensures (p as real) == (a as real) * (b as real)
  {}

  // Product of two positive nats is positive (given the product p).
  lemma MulPosPos(a: nat, b: nat, p: nat)
    requires a > 0 && b > 0 && p == a * b
    ensures p > 0
  {
    MulLowerBound(a, b);   // a >= 1, b > 0 ==> a*b >= b > 0
  }

  // Negating the numerator negates the fraction.
  lemma NegFrac(a: real, b: real)
    requires b != 0.0
    ensures (-a) / b == -(a / b)
  {}

  // Real sign-cast identity for the reduction: if the integers iNew, iOld and
  // the nat factor vg satisfy iNew == s*vqa, iOld == s*vn (s == 1 or -1) and
  // vn == vqa*vg, then (iNew as real)*(vg as real) == iOld as real.
  lemma SignCastMul(iNew: int, iOld: int, vqa: nat, vg: nat, vn: nat, neg: bool)
    requires vn == vqa * vg
    requires iNew == (if neg then -(vqa as int) else vqa as int)
    requires iOld == (if neg then -(vn as int) else vn as int)
    ensures (iNew as real) * (vg as real) == iOld as real
  {
    CastMul(vqa, vg);
    assert (vn as real) == (vqa as real) * (vg as real);
  }

  // Final real identity of the gcd reduction: the reduced fraction nn/qdr equals
  // the original no/vd. Given no == nn*gr and vd == qdr*gr with qdr,gr > 0.
  lemma ReduceFracReal(nn: real, no: real, qdr: real, gr: real, vd: real)
    requires qdr > 0.0 && gr > 0.0
    requires no == nn * gr
    requires vd == qdr * gr
    ensures nn / qdr == no / vd
  {
    RealCancel(nn, qdr, gr);   // (nn*gr)/(qdr*gr) == nn/qdr
    assert no / vd == (nn * gr) / (qdr * gr);
  }

  // Pure-nat core of the gcd reduction. g divides va and vd (as the plain
  // existential `exists k :: n == vg*k`, i.e. BigNatGCD.DividesNat unfolded), and
  // DivMod gave va == vqa*g + vra (vra < g), vd == vqd*g + vrd (vrd < g). Then the
  // remainders vanish, the quotients are exact, and vqd > 0 (vd > 0).
  //
  // The witnesses ka, kd are extracted HERE, inside a module with no bignum
  // axioms in scope, so the nonlinear `:|` does not destabilise Z3 (doing it in
  // the Rational seq-wrapper, where Value's recursive axioms are visible, times
  // out).
  lemma ReduceExactNat(va: nat, vd: nat, vg: nat,
                       vqa: nat, vra: nat, vqd: nat, vrd: nat)
    requires vg > 0 && vd > 0
    requires exists k: nat :: va == vg * k
    requires exists k: nat :: vd == vg * k
    requires va == vqa * vg + vra && vra < vg
    requires vd == vqd * vg + vrd && vrd < vg
    ensures vra == 0 && vrd == 0
    ensures va == vqa * vg
    ensures vd == vqd * vg
    ensures vqd > 0
  {
    var ka :| va == vg * ka;
    var kd :| vd == vg * kd;
    ExactQuotient(va, vg, vqa, vra, ka);
    ExactQuotient(vd, vg, vqd, vrd, kd);
    if vqd == 0 {
      // vd == 0*vg == 0, contradicting vd > 0.
      assert vd == vqd * vg;
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Coprimality of the reduced numerator/denominator. Divisibility is the plain
  // existential `exists k :: n == d*k` (matching BigNatGCD.DividesNat unfolded).
  //////////////////////////////////////////////////////////////////////////////

  // If d divides x (x == d*k), then d*g divides x*g.
  lemma DivMulRight(d: nat, x: nat, g: nat)
    requires exists k: nat :: x == d * k
    ensures exists k: nat :: x * g == (d * g) * k
  {
    var k :| x == d * k;
    MulReassoc(d, k, g);           // (d*k)*g == (d*g)*k
    assert x * g == (d * g) * k;
  }

  // (d*k)*g == (d*g)*k, pure reassociation/commutation of nat multiplication.
  lemma MulReassoc(d: nat, k: nat, g: nat)
    ensures (d * k) * g == (d * g) * k
  {}

  // If h == d*g divides g (g == h*k) and g > 0, then d == 1 (so d <= 1).
  // Because d*g <= g forces d <= 1, and d >= 1 since d*g == g*k > 0.
  lemma DivisorOfFactorIsOne(d: nat, g: nat)
    requires g > 0
    requires exists k: nat :: g == (d * g) * k
    ensures d == 1
  {
    var k :| g == (d * g) * k;
    // g == d*g*k.  If d == 0: g == 0, contradiction. If d >= 2: d*g*k >= d*g >= 2g > g
    // unless k == 0, but k == 0 gives g == 0. So d == 1.
    if d == 0 {
      assert g == 0 * g * k == 0;
    } else if d >= 2 {
      if k == 0 {
        assert g == 0;
      } else {
        // k >= 1: (d*g)*k >= d*g >= 2*g > g.
        MulMonoRight(1, k, d * g);        // d*g <= (d*g)*k
        assert d * g <= (d * g) * k;
        MulMonoRight(2, d, g);            // 2*g <= d*g
        assert 2 * g <= d * g;
      }
    }
  }
}

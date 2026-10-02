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

  // Integer version: product of two positive ints is positive.
  lemma MulPosPosInt(a: int, b: int)
    requires a > 0 && b > 0
    ensures a * b > 0
  {}

  // Difference of two fractions over a common cross-denominator.
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

  //////////////////////////////////////////////////////////////////////////////
  // Fraction-operation bridges, stated over PLAIN ints a,b,c,d (num/den values).
  // DafnyReal binds the IntValue projections to these ints up front and calls
  // these, so the recursive IntValue/Value axioms are never in scope while the
  // nonlinear real division is reasoned about.  b,d > 0 throughout.
  //////////////////////////////////////////////////////////////////////////////

  // Addition: (a*d + c*b)/(b*d) == a/b + c/d.  The caller passes the formed
  // integer products ad == a*d, cb == c*b, bd == b*d, num == ad+cb.
  lemma AddBridge(a: int, b: int, c: int, d: int, ad: int, cb: int, bd: int, num: int)
    requires b > 0 && d > 0
    requires ad == a * d && cb == c * b && bd == b * d && num == ad + cb
    ensures (num as real) / (bd as real)
            == (a as real) / (b as real) + (c as real) / (d as real)
  {
    CastProdInt(ad, a, d);
    CastProdInt(cb, c, b);
    CastProdInt(bd, b, d);
    assert (b as real) != 0.0 && (d as real) != 0.0;
    RealAddFrac(a as real, b as real, c as real, d as real);
  }

  // Subtraction: (a*d - c*b)/(b*d) == a/b - c/d.
  lemma SubBridge(a: int, b: int, c: int, d: int, ad: int, cb: int, bd: int, num: int)
    requires b > 0 && d > 0
    requires ad == a * d && cb == c * b && bd == b * d && num == ad - cb
    ensures (num as real) / (bd as real)
            == (a as real) / (b as real) - (c as real) / (d as real)
  {
    CastProdInt(ad, a, d);
    CastProdInt(cb, c, b);
    CastProdInt(bd, b, d);
    assert (b as real) != 0.0 && (d as real) != 0.0;
    RealSubFrac(a as real, b as real, c as real, d as real);
  }

  // Multiplication: (a*c)/(b*d) == (a/b)*(c/d).
  lemma MulBridge(a: int, b: int, c: int, d: int, ac: int, bd: int)
    requires b > 0 && d > 0
    requires ac == a * c && bd == b * d
    ensures (ac as real) / (bd as real)
            == ((a as real) / (b as real)) * ((c as real) / (d as real))
  {
    CastProdInt(ac, a, c);
    CastProdInt(bd, b, d);
    assert (b as real) != 0.0 && (d as real) != 0.0;
    RealMulFrac(a as real, b as real, c as real, d as real);
  }

  // Comparison: sign of (a*d - c*b) orders a/b vs c/d (b,d > 0).
  lemma CompareBridge(a: int, b: int, c: int, d: int, ad: int, cb: int)
    requires b > 0 && d > 0
    requires ad == a * d && cb == c * b
    ensures (ad < cb) <==> ((a as real) / (b as real) < (c as real) / (d as real))
    ensures (ad == cb) <==> ((a as real) / (b as real) == (c as real) / (d as real))
    ensures (ad > cb) <==> ((a as real) / (b as real) > (c as real) / (d as real))
  {
    CastProdInt(ad, a, d);
    CastProdInt(cb, c, b);
    assert (b as real) > 0.0 && (d as real) > 0.0;
    RealCompareFrac(a as real, b as real, c as real, d as real);
  }

  // Normalize bridge: a == aa/dd, given aa == a*yy, dd == b*yy with b,yy > 0.
  // (aa/dd == (a*yy)/(b*yy) == a/b.)
  lemma SameValueScaled(a: int, b: int, yy: int, aa: int, dd: int)
    requires b > 0 && yy > 0
    requires aa == a * yy && dd == b * yy
    ensures (aa as real) / (dd as real) == (a as real) / (b as real)
  {
    CastProdInt(aa, a, yy);
    CastProdInt(dd, b, yy);
    assert (b as real) != 0.0 && (yy as real) != 0.0;
    RealCancel(a as real, b as real, yy as real);
  }

  // b * yy > 0 for positive ints (denominator of a normalized pair).
  lemma MulPosScale(b: int, yy: int)
    requires b > 0 && yy > 0
    ensures b * yy > 0
  {}

  //////////////////////////////////////////////////////////////////////////////
  // Powers of ten — numeric core of the decimal-printing path.
  //////////////////////////////////////////////////////////////////////////////

  // (xx*g)*yy == (yy*g)*xx, integer reassociation (for Normalize denominators).
  lemma MulReassocInt(xx: int, g: int, yy: int)
    ensures (xx * g) * yy == (yy * g) * xx
  {}

  // Same-denominator addition: (aa+bb)/dd == aa/dd + bb/dd (dd != 0).
  lemma SameDenomAdd(aa: int, bb: int, dd: int, num: int)
    requires dd > 0 && num == aa + bb
    ensures (num as real) / (dd as real)
            == (aa as real) / (dd as real) + (bb as real) / (dd as real)
  {}

  lemma SameDenomSub(aa: int, bb: int, dd: int, num: int)
    requires dd > 0 && num == aa - bb
    ensures (num as real) / (dd as real)
            == (aa as real) / (dd as real) - (bb as real) / (dd as real)
  {}

  // Same-denominator comparison (dd > 0): order of aa/dd vs bb/dd is order of aa vs bb.
  lemma SameDenomCompare(aa: int, bb: int, dd: int)
    requires dd > 0
    ensures (aa < bb) <==> ((aa as real) / (dd as real) < (bb as real) / (dd as real))
    ensures (aa == bb) <==> ((aa as real) / (dd as real) == (bb as real) / (dd as real))
    ensures (aa > bb) <==> ((aa as real) / (dd as real) > (bb as real) / (dd as real))
  {}

  // Reciprocal of a positive-numerator fraction: den/num == 1/(num/den) when num>0, den>0.
  lemma ReciprocalFrac(num: real, den: real)
    requires num > 0.0 && den > 0.0
    ensures den / num == 1.0 / (num / den)
  {}

  // Reciprocal when num < 0: (-den)/(-num) == 1/(num/den). den > 0, num < 0.
  lemma ReciprocalFracNeg(num: real, den: real)
    requires num < 0.0 && den > 0.0
    ensures (-den) / (-num) == 1.0 / (num / den)
  {}

  // Division as multiplication by the reciprocal: x * (1/y) == x/y (y != 0).
  lemma DivIsMulRecip(x: real, y: real)
    requires y != 0.0
    ensures x * (1.0 / y) == x / y
  {}

  // 10^n as a nat.
  function Pow10(n: nat): nat
  {
    if n == 0 then 1 else 10 * Pow10(n - 1)
  }

  lemma Pow10Positive(n: nat)
    ensures Pow10(n) >= 1
  {
    if n == 0 {} else { Pow10Positive(n - 1); }
  }

  // IsPowerOf10 over nat, matching C# BigRational.IsPowerOf10: returns (yes, log10)
  // and, when yes, proves x == Pow10(log10). This is the numeric core of the
  // "print as a terminating decimal" test.
  function IsPowerOf10(x: nat): (res: (bool, nat))
    decreases x
  {
    if x == 0 then (false, 0)
    else if x == 1 then (true, 0)
    else if x % 10 == 0 then
      var (yes, l) := IsPowerOf10(x / 10);
      if yes then (true, l + 1) else (false, 0)
    else (false, 0)
  }

  // Correctness of IsPowerOf10: a true answer means x is exactly that power of ten.
  lemma IsPowerOf10Correct(x: nat)
    ensures var (yes, l) := IsPowerOf10(x); yes ==> x == Pow10(l)
    decreases x
  {
    var (yes, l) := IsPowerOf10(x);
    if x == 0 {
    } else if x == 1 {
    } else if x % 10 == 0 {
      var (yes', l') := IsPowerOf10(x / 10);
      if yes' {
        IsPowerOf10Correct(x / 10);           // x/10 == Pow10(l')
        assert x / 10 == Pow10(l');
        assert x == 10 * (x / 10);            // x % 10 == 0
        assert Pow10(l' + 1) == 10 * Pow10(l');
      }
    }
  }

  // DividesAPowerOf10 over nat, matching C# BigRational.DividesAPowerOf10.
  // When it returns (true, factor, log10), it proves factor * i == Pow10(log10),
  // i.e. i divides a power of ten (so the fraction num/i terminates in decimal).
  function DividesAPowerOf10(i: nat): (res: (bool, nat, nat))
    requires i > 0
    decreases i
  {
    if i == 1 then (true, 1, 0)
    else if i % 10 == 0 then
      var (ok, f, l) := DividesAPowerOf10(i / 10);
      if ok then (true, f, l + 1) else (false, 0, 0)
    else if i % 5 == 0 then
      var (ok, f, l) := DividesAPowerOf10(i / 5);
      if ok then (true, 2 * f, l + 1) else (false, 0, 0)
    else if i % 2 == 0 then
      var (ok, f, l) := DividesAPowerOf10(i / 2);
      if ok then (true, 5 * f, l + 1) else (false, 0, 0)
    else (false, 0, 0)
  }

  // Correctness: a true answer gives factor * i == Pow10(log10).
  lemma DividesAPowerOf10Correct(i: nat)
    requires i > 0
    ensures var (ok, f, l) := DividesAPowerOf10(i); ok ==> f * i == Pow10(l)
    decreases i
  {
    var (ok, f, l) := DividesAPowerOf10(i);
    if i == 1 {
      // f == 1, l == 0, Pow10(0) == 1 == 1*1.
    } else if i % 10 == 0 {
      var (ok', f', l') := DividesAPowerOf10(i / 10);
      if ok' {
        DividesAPowerOf10Correct(i / 10);        // f' * (i/10) == Pow10(l')
        TenStep(i, f');                          // f' * i == 10 * (f' * (i/10))
        assert Pow10(l' + 1) == 10 * Pow10(l');
      }
    } else if i % 5 == 0 {
      var (ok', f', l') := DividesAPowerOf10(i / 5);
      if ok' {
        DividesAPowerOf10Correct(i / 5);         // f' * (i/5) == Pow10(l')
        FiveStep(i, f');                         // (2*f')*i == 10*(f'*(i/5))
        assert Pow10(l' + 1) == 10 * Pow10(l');
      }
    } else if i % 2 == 0 {
      var (ok', f', l') := DividesAPowerOf10(i / 2);
      if ok' {
        DividesAPowerOf10Correct(i / 2);         // f' * (i/2) == Pow10(l')
        TwoStep(i, f');                          // (5*f')*i == 10*(f'*(i/2))
        assert Pow10(l' + 1) == 10 * Pow10(l');
      }
    }
  }

  // f*i == 10*(f*(i/10)) when 10 | i.
  lemma TenStep(i: nat, f: nat)
    requires i % 10 == 0
    ensures f * i == 10 * (f * (i / 10))
  {
    assert i == 10 * (i / 10);
    MulReassocNat(f, 10, i / 10);
  }

  // (2*f)*i == 10*(f*(i/5)) when 5 | i.
  lemma FiveStep(i: nat, f: nat)
    requires i % 5 == 0
    ensures (2 * f) * i == 10 * (f * (i / 5))
  {
    assert i == 5 * (i / 5);
  }

  // (5*f)*i == 10*(f*(i/2)) when 2 | i.
  lemma TwoStep(i: nat, f: nat)
    requires i % 2 == 0
    ensures (5 * f) * i == 10 * (f * (i / 2))
  {
    assert i == 2 * (i / 2);
  }

  // f*(a*b) == a*(f*b), nat reassociation.
  lemma MulReassocNat(f: nat, a: nat, b: nat)
    ensures f * (a * b) == a * (f * b)
  {}
}

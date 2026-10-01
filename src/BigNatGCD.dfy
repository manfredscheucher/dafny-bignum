/*******************************************************************************
 * dafny-bignum: BigNatGCD
 *
 * Euclidean greatest common divisor on unsigned BigNat, specified against a
 * mathematical gcd predicate on nat and proved correct.
 *
 *   GCD(a, b) = if b == 0 then a else GCD(b, a mod b)
 *
 * The remainder a mod b comes from the verified DivMod (a == q*b + r,
 * 0 <= r < b). Termination is by Value(b) (the remainder strictly decreases).
 *
 * All number-theoretic reasoning is over nat (Value(...) read as a nat). The
 * nonlinear facts (n == d*k) are confined to pure-nat helper lemmas, following
 * the repo convention of keeping Value() out of nonlinear contexts.
 *******************************************************************************/

include "BigNat.dfy"
include "BigNatAddSub.dfy"
include "BigNatDivMod.dfy"

module BigNatGCD {
  import opened BigNat
  import opened BigNatAddSub
  import opened BigNatDivMod

  //////////////////////////////////////////////////////////////////////////////
  // Mathematical divisibility and gcd, over nat.
  //////////////////////////////////////////////////////////////////////////////

  // d divides n: n is a nat multiple of d. With d == 0 this forces n == 0, so
  // DividesNat(0, n) <==> n == 0, exactly as gcd needs.
  ghost predicate DividesNat(d: nat, n: nat)
  {
    exists k: nat :: n == d * k
  }

  // g is THE greatest common divisor of a and b: it divides both, and every
  // common divisor divides it.
  ghost predicate IsGCD(g: nat, a: nat, b: nat)
  {
    && DividesNat(g, a)
    && DividesNat(g, b)
    && (forall d: nat :: DividesNat(d, a) && DividesNat(d, b) ==> DividesNat(d, g))
  }

  //////////////////////////////////////////////////////////////////////////////
  // The function.
  //////////////////////////////////////////////////////////////////////////////

  function GCD(xs: seq<limb>, ys: seq<limb>): (g: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    ensures Normalized(g)
    ensures IsGCD(Value(g), Value(xs), Value(ys))
    decreases Value(ys)
  {
    if IsZero(ys) then
      GCDBaseZero(xs, ys);
      xs
    else
      // ys != 0, so Value(ys) > 0 (normalized nonempty).
      NonEmptyPositive(ys);
      var (q, r) := DivMod(xs, ys);
      // a == q*b + r, 0 <= r < b. The step lemma transfers the gcd spec.
      GCDStep(xs, ys, q, r);
      GCD(ys, r)
  }

  //////////////////////////////////////////////////////////////////////////////
  // Correctness of the two cases.
  //////////////////////////////////////////////////////////////////////////////

  // Base case: gcd(a, 0) == a.
  lemma GCDBaseZero(xs: seq<limb>, ys: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    requires IsZero(ys)
    ensures IsGCD(Value(xs), Value(xs), Value(ys))
  {
    var a := Value(xs);
    assert Value(ys) == 0;
    // a | a (k == 1), a | 0 (k == 0), and any common divisor of a and 0 divides a.
    DividesReflexive(a);
    DividesZero(a);
  }

  // Recursive step: IsGCD(g, b, r) ==> IsGCD(g, a, b) when a == q*b + r.
  // Here the recursive call gives IsGCD(Value(GCD(ys,r)), Value(ys), Value(r));
  // we need IsGCD(same g, Value(xs), Value(ys)). Both directions of
  // "common divisors of (a,b) == common divisors of (b,r)" are needed.
  lemma GCDStep(xs: seq<limb>, ys: seq<limb>, q: seq<limb>, r: seq<limb>)
    requires Normalized(xs) && Normalized(ys) && Normalized(q) && Normalized(r)
    requires Value(xs) == Value(q) * Value(ys) + Value(r)
    ensures forall g: nat ::
              IsGCD(g, Value(ys), Value(r)) ==> IsGCD(g, Value(xs), Value(ys))
  {
    var a := Value(xs);
    var b := Value(ys);
    var qq := Value(q);
    var rr := Value(r);
    assert a == qq * b + rr;
    forall g: nat | IsGCD(g, b, rr)
      ensures IsGCD(g, a, b)
    {
      GCDStepOne(a, b, qq, rr, g);
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Pure-nat number theory. Value() never appears below this line, so the
  // nonlinear multiplication is handled where the solver is stable.
  //////////////////////////////////////////////////////////////////////////////

  // Single instance of the step, entirely over nat: a == q*b + r and g a gcd of
  // (b, r) make g a gcd of (a, b).
  lemma GCDStepOne(a: nat, b: nat, q: nat, r: nat, g: nat)
    requires a == q * b + r
    requires IsGCD(g, b, r)
    ensures IsGCD(g, a, b)
  {
    // g divides b and r, hence g divides a == q*b + r.
    assert DividesNat(g, b);
    assert DividesNat(g, r);
    DividesLinear(g, b, r, q);          // g | (q*b + r) == a
    assert DividesNat(g, a);
    // Every common divisor d of a and b also divides r == a - q*b, hence (b,r),
    // hence g.
    forall d: nat | DividesNat(d, a) && DividesNat(d, b)
      ensures DividesNat(d, g)
    {
      DividesRemainder(d, a, b, q, r);  // d | a && d | b ==> d | r
      assert DividesNat(d, b) && DividesNat(d, r);
      // g is gcd of (b, r), so d | g.
      assert DividesNat(d, g);
    }
  }

  // g | b && g | r  ==>  g | (q*b + r).
  lemma DividesLinear(g: nat, b: nat, r: nat, q: nat)
    requires DividesNat(g, b) && DividesNat(g, r)
    ensures DividesNat(g, q * b + r)
  {
    var kb :| b == g * kb;
    var kr :| r == g * kr;
    // q*b + r == q*(g*kb) + g*kr == g*(q*kb + kr).
    calc {
      q * b + r;
      q * (g * kb) + g * kr;
      { MulShuffle(q, g, kb); }     // q*(g*kb) == g*(q*kb)
      g * (q * kb) + g * kr;
      { DistribLeft(g, q * kb, kr); }
      g * (q * kb + kr);
    }
    assert q * b + r == g * (q * kb + kr);
    assert DividesNat(g, q * b + r) by {
      var k := q * kb + kr;
      assert q * b + r == g * k;
    }
  }

  // d | a && d | b && a == q*b + r  ==>  d | r.  (r == a - q*b.)
  lemma DividesRemainder(d: nat, a: nat, b: nat, q: nat, r: nat)
    requires a == q * b + r
    requires DividesNat(d, a) && DividesNat(d, b)
    ensures DividesNat(d, r)
  {
    var ka :| a == d * ka;
    var kb :| b == d * kb;
    // r == a - q*b == d*ka - q*(d*kb) == d*ka - d*(q*kb) == d*(ka - q*kb).
    // ka - q*kb is a nat because r >= 0 and r == d*(ka - q*kb).
    MulShuffle(q, d, kb);               // q*(d*kb) == d*(q*kb)
    assert q * b == d * (q * kb);
    assert r == a - q * b;
    assert a == d * ka;
    // d*ka >= d*(q*kb) since a == q*b + r >= q*b.
    DividesRemainderWitness(d, ka, q * kb, r);
  }

  // From r == d*ka - d*m and r >= 0, exhibit r == d*(ka - m) with ka - m a nat.
  lemma DividesRemainderWitness(d: nat, ka: nat, m: nat, r: nat)
    requires r == d * ka - d * m
    requires r >= 0
    requires d * ka >= d * m
    ensures DividesNat(d, r)
  {
    DistribLeft(d, ka, m);              // when ka >= m: d*(ka-m) == d*ka - d*m
    if ka >= m {
      assert r == d * (ka - m);
      assert DividesNat(d, r) by {
        var k := ka - m;
        assert r == d * k;
      }
    } else {
      // ka < m would give d*ka < d*m when d > 0, contradicting the hypothesis;
      // if d == 0 then d*ka == d*m == 0 == r, divisible trivially.
      if d == 0 {
        assert r == 0;
        assert DividesNat(d, r) by { assert r == d * 0; }
      } else {
        MulStrictMono(d, ka, m);        // ka < m && d > 0 ==> d*ka < d*m
        assert false;
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Small divisibility facts.
  //////////////////////////////////////////////////////////////////////////////

  lemma DividesReflexive(a: nat)
    ensures DividesNat(a, a)
  {
    assert a == a * 1;
  }

  lemma DividesZero(a: nat)
    ensures DividesNat(a, 0)
  {
    assert 0 == a * 0;
  }

  //////////////////////////////////////////////////////////////////////////////
  // Pure nonlinear arithmetic helpers (no Value, no recursion).
  //////////////////////////////////////////////////////////////////////////////

  lemma MulShuffle(a: nat, b: nat, c: nat)
    ensures a * (b * c) == b * (a * c)
  {
    MulAssoc(a, b, c);                  // a*(b*c) == (a*b)*c
    assert a * b == b * a by { MulCommG(a, b); }
    MulAssoc(b, a, c);                  // b*(a*c) == (b*a)*c
  }

  lemma DistribLeft(a: nat, p: nat, q: nat)
    ensures a * (p + q) == a * p + a * q
  {}

  lemma MulCommG(a: nat, b: nat)
    ensures a * b == b * a
  {}

  lemma MulStrictMono(d: nat, a: nat, b: nat)
    requires d > 0 && a < b
    ensures d * a < d * b
  {}

  //////////////////////////////////////////////////////////////////////////////
  // Representation bridge.
  //////////////////////////////////////////////////////////////////////////////

  // A normalized nonempty sequence has strictly positive Value.
  lemma NonEmptyPositive(ys: seq<limb>)
    requires Normalized(ys) && !IsZero(ys)
    ensures Value(ys) > 0
  {
    if Value(ys) == 0 {
      NormalizedZeroUnique(ys);
      assert ys == [];
    }
  }
}

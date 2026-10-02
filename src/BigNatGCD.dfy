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
  @IsolateAssertions
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

  //////////////////////////////////////////////////////////////////////////////
  // Least-absolute-remainder variant.
  //
  // Same spec as GCD, but each step replaces the remainder r = a mod b by the
  // smaller of r and b-r (both in [0, b)), so the remainder at least halves
  // every step instead of following the Fibonacci worst case. gcd(b, b-r) ==
  // gcd(b, r) because a common divisor of b and r divides b-r and vice versa,
  // so the result is unchanged. Still O(1) extra work per step; only the step
  // count improves. GCD above is kept as the reference implementation.
  //////////////////////////////////////////////////////////////////////////////

  function GCDFast(xs: seq<limb>, ys: seq<limb>): (g: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    ensures Normalized(g)
    ensures IsGCD(Value(g), Value(xs), Value(ys))
    decreases Value(ys)
  {
    if IsZero(ys) then
      GCDBaseZero(xs, ys);
      xs
    else
      NonEmptyPositive(ys);
      var (q, r) := DivMod(xs, ys);
      // 0 <= Value(r) < Value(ys), so Sub(ys, r) is legal and bMinusR = ys - r.
      var bMinusR := Sub(ys, r);
      if Compare(r, bMinusR) <= 0 then
        // rSmall == r < ys: ordinary Euclid step.
        GCDStep(xs, ys, q, r);
        GCDFast(ys, r)
      else
        // rSmall == b - r. Compare > 0 gives Value(r) > Value(bMinusR), so
        // Value(r) > 0 and hence Value(bMinusR) == ys - r < ys (termination).
        SubBranchDecr(ys, r, bMinusR);
        GCDFastStepSub(xs, ys, q, r, bMinusR);
        GCDFast(ys, bMinusR)
  }

  // In the b-r branch Value(r) > Value(bMinusR) == Value(ys) - Value(r), which
  // forces Value(bMinusR) < Value(ys). Isolated so the decreases check sees a
  // plain nat inequality.
  lemma SubBranchDecr(ys: seq<limb>, r: seq<limb>, bMinusR: seq<limb>)
    requires Normalized(ys) && Normalized(r) && Normalized(bMinusR)
    requires Value(bMinusR) == Value(ys) - Value(r)
    requires Value(r) < Value(ys)
    requires Value(r) > Value(bMinusR)
    ensures Value(bMinusR) < Value(ys)
  {
    // Value(r) > Value(ys) - Value(r) ==> 2*Value(r) > Value(ys) > 0 ==>
    // Value(r) > 0 ==> Value(ys) - Value(r) < Value(ys).
  }

  // Transfers the gcd spec across one GCDFast step and justifies termination.
  // rSmall is r or (ys - r); either way its common divisors with ys match those
  // of r, so IsGCD(g, ys, rSmall) ==> IsGCD(g, xs, ys), and Value(rSmall) < ys.
  // The b-r branch: gcd(ys, ys-r) == gcd(ys, r) == gcd(xs, ys). Same forall-shape
  // as GCDStep (which verifies), with one extra reflection lemma per divisor.
  lemma GCDFastStepSub(xs: seq<limb>, ys: seq<limb>, q: seq<limb>, r: seq<limb>,
                       bMinusR: seq<limb>)
    requires Normalized(xs) && Normalized(ys) && Normalized(q) && Normalized(r)
    requires Normalized(bMinusR)
    requires Value(xs) == Value(q) * Value(ys) + Value(r)
    requires Value(r) < Value(ys)
    requires Value(bMinusR) == Value(ys) - Value(r)
    ensures forall g: nat ::
              IsGCD(g, Value(ys), Value(bMinusR)) ==> IsGCD(g, Value(xs), Value(ys))
  {
    var a := Value(xs);
    var b := Value(ys);
    var qq := Value(q);
    var rr := Value(r);
    forall g: nat | IsGCD(g, b, b - rr)
      ensures IsGCD(g, a, b)
    {
      GCDSubReflect(b, rr, g);        // IsGCD(g, b, b-rr) ==> IsGCD(g, b, rr)
      GCDStepOne(a, b, qq, rr, g);    // ==> IsGCD(g, a, b)
    }
  }

  // gcd(b, b-r) and gcd(b, r) have the same common divisors, so a gcd of one is
  // a gcd of the other. Pure nat; needs r <= b.
  lemma GCDSubReflect(b: nat, r: nat, g: nat)
    requires r <= b
    requires IsGCD(g, b, b - r)
    ensures IsGCD(g, b, r)
  {
    // g divides b and (b-r), hence r == b - (b-r).
    assert DividesNat(g, b);
    assert DividesNat(g, b - r);
    DividesSub(g, b, b - r, r);         // g | b && g | (b-r) ==> g | r
    // Any common divisor d of (b, r) also divides (b-r), so it divides g.
    forall d: nat | DividesNat(d, b) && DividesNat(d, r)
      ensures DividesNat(d, g)
    {
      DividesSub(d, b, r, b - r);       // d | b && d | r ==> d | (b-r)
      assert DividesNat(d, b) && DividesNat(d, b - r);
      assert DividesNat(d, g);          // g gcd of (b, b-r)
    }
  }

  // g | x && g | y && z == x - y (x >= y)  ==>  g | z.
  lemma DividesSub(g: nat, x: nat, y: nat, z: nat)
    requires x >= y && z == x - y
    requires DividesNat(g, x) && DividesNat(g, y)
    ensures DividesNat(g, z)
  {
    var kx :| x == g * kx;
    var ky :| y == g * ky;
    // z == x - y == g*kx - g*ky == g*(kx - ky), and z >= 0.
    DividesRemainderWitness(g, kx, ky, z);
  }
}

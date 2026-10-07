/*******************************************************************************
 * dafny-bignum / fixed-width: FwGCD
 *
 * Euclidean greatest common divisor over the fixed-width BigNat stack. Mirrors
 * the proven algorithm of src/BigNatGCD.dfy, but the only executable value is a
 * seq<limb> (and the recursion runs on the DivMod remainder, never a nat/int
 * counter), so the generated code stays Boost-free.
 *
 *   GCD(a, b) = if b == 0 then a else GCD(b, a mod b)
 *
 * [] is the normalized zero, so the zero test is |ys| == 0 (no element index).
 * Termination is by Value(b) (ghost). All number theory is over nat in ghost
 * lemmas; the nonlinear facts (n == d*k) stay in pure-nat helpers.
 *******************************************************************************/

include "FwNat.dfy"
include "FwDivMod.dfy"

module FwGCD {
  import opened FwNat
  import opened FwDivMod

  //////////////////////////////////////////////////////////////////////////////
  // Mathematical divisibility and gcd, over nat (ghost).
  //////////////////////////////////////////////////////////////////////////////

  ghost predicate DividesNat(d: nat, n: nat)
  {
    exists k: nat :: n == d * k
  }

  ghost predicate IsGCD(g: nat, a: nat, b: nat)
  {
    && DividesNat(g, a)
    && DividesNat(g, b)
    && (forall d: nat :: DividesNat(d, a) && DividesNat(d, b) ==> DividesNat(d, g))
  }

  //////////////////////////////////////////////////////////////////////////////
  // The method. Executable value is seq<limb> only; zero test is |ys| == 0.
  //////////////////////////////////////////////////////////////////////////////

  method GCD(xs: seq<limb>, ys: seq<limb>) returns (g: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    ensures Normalized(g)
    ensures IsGCD(Value(g), Value(xs), Value(ys))
    decreases Value(ys)
  {
    if |ys| == 0 {
      GCDBaseZero(xs, ys);
      return xs;
    }
    // ys != [] and normalized, so Value(ys) > 0.
    NonEmptyPositive(ys);
    var q, r := DivMod(xs, ys);
    // a == q*b + r, 0 <= r < b. Termination: Value(r) < Value(ys).
    GCDStep(xs, ys, q, r);
    g := GCD(ys, r);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Correctness of the two cases.
  //////////////////////////////////////////////////////////////////////////////

  // Base case: gcd(a, 0) == a.
  lemma GCDBaseZero(xs: seq<limb>, ys: seq<limb>)
    requires Normalized(xs) && Normalized(ys)
    requires |ys| == 0
    ensures IsGCD(Value(xs), Value(xs), Value(ys))
  {
    var a := Value(xs);
    assert Value(ys) == 0;
    DividesReflexive(a);
    DividesZero(a);
  }

  // Recursive step: IsGCD(g, b, r) ==> IsGCD(g, a, b) when a == q*b + r.
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
  // Pure-nat number theory. Value() never appears below this line.
  //////////////////////////////////////////////////////////////////////////////

  lemma GCDStepOne(a: nat, b: nat, q: nat, r: nat, g: nat)
    requires a == q * b + r
    requires IsGCD(g, b, r)
    ensures IsGCD(g, a, b)
  {
    assert DividesNat(g, b);
    assert DividesNat(g, r);
    DividesLinear(g, b, r, q);          // g | (q*b + r) == a
    assert DividesNat(g, a);
    forall d: nat | DividesNat(d, a) && DividesNat(d, b)
      ensures DividesNat(d, g)
    {
      DividesRemainder(d, a, b, q, r);  // d | a && d | b ==> d | r
      assert DividesNat(d, b) && DividesNat(d, r);
      assert DividesNat(d, g);
    }
  }

  // g | b && g | r  ==>  g | (q*b + r).
  lemma DividesLinear(g: nat, b: nat, r: nat, q: nat)
    requires DividesNat(g, b) && DividesNat(g, r)
    ensures DividesNat(g, q * b + r)
  {
    var kb: nat :| b == g * kb;
    var kr: nat :| r == g * kr;
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

  // d | a && d | b && a == q*b + r  ==>  d | r.
  lemma DividesRemainder(d: nat, a: nat, b: nat, q: nat, r: nat)
    requires a == q * b + r
    requires DividesNat(d, a) && DividesNat(d, b)
    ensures DividesNat(d, r)
  {
    var ka: nat :| a == d * ka;
    var kb: nat :| b == d * kb;
    MulShuffle(q, d, kb);               // q*(d*kb) == d*(q*kb)
    assert q * b == d * (q * kb);
    assert r == a - q * b;
    assert a == d * ka;
    DividesRemainderWitness(d, ka, q * kb, r);
  }

  // From r == d*ka - d*m and r >= 0, exhibit r == d*(ka - m) with ka - m a nat.
  lemma DividesRemainderWitness(d: nat, ka: nat, m: nat, r: nat)
    requires r == d * ka - d * m
    requires r >= 0
    requires d * ka >= d * m
    ensures DividesNat(d, r)
  {
    DistribLeft(d, ka, m);
    if ka >= m {
      assert r == d * (ka - m);
      assert DividesNat(d, r) by {
        var k := ka - m;
        assert r == d * k;
      }
    } else {
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
    MulAssocG(a, b, c);
    assert a * b == b * a by { MulCommG(a, b); }
    MulAssocG(b, a, c);
  }

  lemma MulAssocG(a: nat, b: nat, c: nat)
    ensures a * (b * c) == (a * b) * c
  {}

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
  // Representation bridge: a normalized nonempty sequence has positive Value.
  //////////////////////////////////////////////////////////////////////////////

  lemma NonEmptyPositive(ys: seq<limb>)
    requires Normalized(ys) && |ys| != 0
    ensures Value(ys) > 0
  {
    if Value(ys) == 0 {
      NormalizedZeroUnique(ys);
      assert ys == [];
    }
  }

  // A normalized sequence whose Value is 0 must be [].
  lemma NormalizedZeroUnique(xs: seq<limb>)
    requires Normalized(xs) && Value(xs) == 0
    ensures xs == []
    decreases |xs|
  {
    if |xs| != 0 {
      // Value(xs) == xs[0] + BASE*Value(xs[1..]) == 0, both summands >= 0.
      assert (xs[0] as nat) == 0;
      assert Value(xs[1..]) == 0;
      if |xs| == 1 {
        // then xs == [0], but Normalized requires xs[0] != 0 — contradiction.
        assert xs[|xs| - 1] == xs[0];
        assert (xs[0] as nat) == 0;
        assert xs[0] == 0;
      } else {
        // xs[1..] is normalized (shares the top limb) and has Value 0.
        assert xs[1..][|xs[1..]| - 1] == xs[|xs| - 1];
        NormalizedZeroUnique(xs[1..]);
        assert xs[1..] == [];
        assert |xs| == 1;
      }
    }
  }
}

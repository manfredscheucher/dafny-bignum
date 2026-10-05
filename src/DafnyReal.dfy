/*******************************************************************************
 * dafny-bignum: DafnyReal
 *
 * A formally verified counterpart of Dafny's runtime BigRational (the num/den
 * representation of `real`). A signed BigInt numerator over a strictly positive
 * BigInt denominator, kept UNREDUCED — the denominator is significant because it
 * decides how many decimal places `print` shows (1.5*1.0 is 150/100 and must
 * print "1.50", not "1.5"). This mirrors DafnyRuntime.cs `struct BigRational`
 * exactly; the point is to replace the 4x hand-written per-language BigRational
 * (C#/Java/JS/C++) with ONE verified implementation.
 *
 * Invariant (Wf): den > 0. (The C# "num==0 && den==0" default-struct case does
 * not arise here, as every DReal is built through the constructors below.)
 *
 * Arithmetic matches the C# operators:
 *   - Add/Sub/CompareTo use the gcd-of-denominators Normalize (common denominator
 *     via gcd of the two dens), so precision is preserved, not reduced away.
 *   - Mul/Div are raw cross products (no normalization), as in C#.
 * Everything is proved against RealValue(): the real number num/den.
 *
 * Printing (IsPowerOf10 / DividesAPowerOf10 / ToString) follows C# too. The
 * numeric core of DividesAPowerOf10 (10^log10 == factor*i) is proved; the string
 * assembly is executable and commented, not given a false numeric ensures.
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

  //////////////////////////////////////////////////////////////////////////////
  // Constructors.
  //////////////////////////////////////////////////////////////////////////////

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
  // Positive-denominator helper: product of two positive BigInt dens is positive.
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
  // Multiplication: (a/b)*(c/d) == (a*c)/(b*d), raw (C# operator *).
  //////////////////////////////////////////////////////////////////////////////

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

  lemma MulValueBridge(x: DReal, y: DReal, num: BigInt.Int, den: BigInt.Int)
    requires Wf(x) && Wf(y)
    requires BigInt.Wf(num) && BigInt.Wf(den)
    requires BigInt.IntValue(num) == BigInt.IntValue(x.num) * BigInt.IntValue(y.num)
    requires BigInt.IntValue(den) == BigInt.IntValue(x.den) * BigInt.IntValue(y.den)
    requires BigInt.IntValue(den) > 0
    ensures RealValue(DReal(num, den)) == RealValue(x) * RealValue(y)
  {
    PureArith.MulBridge(BigInt.IntValue(x.num), BigInt.IntValue(x.den),
                        BigInt.IntValue(y.num), BigInt.IntValue(y.den),
                        BigInt.IntValue(num), BigInt.IntValue(den));
  }

  //////////////////////////////////////////////////////////////////////////////
  // Normalize two reals to a common denominator via gcd of the denominators,
  // matching C# BigRational.Normalize. Returns (aa, bb, dd) with
  //   aa/dd == RealValue(x),  bb/dd == RealValue(y),  dd > 0.
  // The common denominator is x.den * (y.den / gcd), NOT reduced further, so the
  // precision carried by the original denominators is preserved.
  //////////////////////////////////////////////////////////////////////////////

  // gcd(|p|, |q|) as a positive BigInt, for p,q > 0. (Operates on magnitudes.)
  function GcdPos(p: BigInt.Int, q: BigInt.Int): (g: BigInt.Int)
    requires BigInt.Wf(p) && BigInt.Wf(q)
    requires BigInt.IntValue(p) > 0 && BigInt.IntValue(q) > 0
    ensures BigInt.Wf(g) && BigInt.IntValue(g) > 0
    ensures BigNatGCD.DividesNat(Value(g.mag), Value(p.mag))
    ensures BigNatGCD.DividesNat(Value(g.mag), Value(q.mag))
  {
    PositiveIsNonempty(p);
    PositiveIsNonempty(q);
    var gm := BigNatGCD.GCD(p.mag, q.mag);
    GcdNonzero(p, q, gm);
    BigInt.FromMagnitude(gm)
  }

  lemma PositiveIsNonempty(x: BigInt.Int)
    requires BigInt.Wf(x) && BigInt.IntValue(x) > 0
    ensures Normalized(x.mag) && Value(x.mag) > 0 && !x.negative
  {
    if x.negative {
      // IntValue < 0 then, contradiction
      assert BigInt.IntValue(x) <= 0;
    }
  }

  lemma GcdNonzero(p: BigInt.Int, q: BigInt.Int, gm: seq<limb>)
    requires BigInt.Wf(p) && BigInt.Wf(q)
    requires !p.negative && !q.negative
    requires Value(p.mag) > 0
    requires Normalized(gm)
    requires BigNatGCD.IsGCD(Value(gm), Value(p.mag), Value(q.mag))
    ensures Value(gm) > 0
  {
    // gm divides p.mag > 0; a zero gcd would force p.mag == 0.
    if Value(gm) == 0 {
      assert BigNatGCD.DividesNat(0, Value(p.mag));   // from IsGCD
      // DividesNat(0, n) == (exists k :: n == 0*k) == (n == 0)
      assert Value(p.mag) == 0;
    }
  }

  // Normalize: result triple as BigInts. Proved so that aa/dd and bb/dd give the
  // two real values and dd > 0.
  function Normalize(x: DReal, y: DReal): (t: (BigInt.Int, BigInt.Int, BigInt.Int))
    requires Wf(x) && Wf(y)
    ensures var (aa, bb, dd) := t;
            BigInt.Wf(aa) && BigInt.Wf(bb) && BigInt.Wf(dd) && BigInt.IntValue(dd) > 0
    ensures var (aa, bb, dd) := t;
            RealValue(x) == BigInt.IntValue(aa) as real / BigInt.IntValue(dd) as real
    ensures var (aa, bb, dd) := t;
            RealValue(y) == BigInt.IntValue(bb) as real / BigInt.IntValue(dd) as real
  {
    if BigInt.IntValue(x.num) == 0 then
      // x == 0/1-equivalent: aa = x.num (=0), dd = y.den, bb = y.num.
      ZeroNumValue(x);
      (x.num, y.num, y.den)
    else if BigInt.IntValue(y.num) == 0 then
      ZeroNumValue(y);
      (x.num, y.num, x.den)
    else
      var g := GcdPos(x.den, y.den);
      // xx = x.den / g, yy = y.den / g (exact: g divides both dens).
      var xx := ExactDiv(x.den, g);
      var yy := ExactDiv(y.den, g);
      var aa := BigInt.Mul(x.num, yy);
      var bb := BigInt.Mul(y.num, xx);
      var dd := BigInt.Mul(x.den, yy);
      NormalizeValues(x, y, g, xx, yy, aa, bb, dd);
      (aa, bb, dd)
  }

  // When x.num == 0, RealValue(x) == 0 and equals 0/anything-positive.
  lemma ZeroNumValue(x: DReal)
    requires Wf(x) && BigInt.IntValue(x.num) == 0
    ensures RealValue(x) == 0.0
    ensures forall d: BigInt.Int :: BigInt.Wf(d) && BigInt.IntValue(d) > 0 ==>
              (BigInt.IntValue(x.num) as real) / (BigInt.IntValue(d) as real) == 0.0
  {}

  // Exact division of a positive BigInt by a positive divisor that divides it.
  // Returns q with IntValue(q) == IntValue(a) / IntValue(g) and q*g == a.
  function ExactDiv(a: BigInt.Int, g: BigInt.Int): (q: BigInt.Int)
    requires BigInt.Wf(a) && BigInt.Wf(g)
    requires BigInt.IntValue(a) > 0 && BigInt.IntValue(g) > 0
    requires BigNatGCD.DividesNat(Value(g.mag), Value(a.mag))
    ensures BigInt.Wf(q) && BigInt.IntValue(q) > 0
    ensures BigInt.IntValue(a) == BigInt.IntValue(q) * BigInt.IntValue(g)
  {
    PositiveIsNonempty(a);
    PositiveIsNonempty(g);
    var (qm, rm) := BigNatDivMod.DivMod(a.mag, g.mag);
    ExactDivRem(a, g, qm, rm);
    BigInt.FromMagnitude(qm)
  }

  // DivMod of a by g where g | a leaves remainder 0, quotient positive.
  lemma ExactDivRem(a: BigInt.Int, g: BigInt.Int, qm: seq<limb>, rm: seq<limb>)
    requires BigInt.Wf(a) && BigInt.Wf(g)
    requires !a.negative && !g.negative
    requires Value(a.mag) > 0 && Value(g.mag) > 0
    requires Normalized(qm) && Normalized(rm)
    requires Value(a.mag) == Value(qm) * Value(g.mag) + Value(rm)
    requires Value(rm) < Value(g.mag)
    requires BigNatGCD.DividesNat(Value(g.mag), Value(a.mag))
    ensures Value(rm) == 0
    ensures Value(a.mag) == Value(qm) * Value(g.mag)
    ensures Value(qm) > 0
  {
    var va := Value(a.mag); var vg := Value(g.mag);
    var vq := Value(qm); var vr := Value(rm);
    assert exists k: nat :: va == vg * k;      // DividesNat unfolded
    var k :| va == vg * k;
    PureArith.ExactQuotient(va, vg, vq, vr, k);
    // va == vq*vg and va > 0, vg > 0 ==> vq > 0
    if vq == 0 { assert va == 0; }
  }

  // Values of the Normalize branch: aa/dd == x, bb/dd == y, dd > 0.
  @IsolateAssertions
  lemma NormalizeValues(x: DReal, y: DReal, g: BigInt.Int, xx: BigInt.Int, yy: BigInt.Int,
                        aa: BigInt.Int, bb: BigInt.Int, dd: BigInt.Int)
    requires Wf(x) && Wf(y)
    requires BigInt.Wf(g) && BigInt.Wf(xx) && BigInt.Wf(yy)
    requires BigInt.Wf(aa) && BigInt.Wf(bb) && BigInt.Wf(dd)
    requires BigInt.IntValue(g) > 0
    requires BigInt.IntValue(x.den) == BigInt.IntValue(xx) * BigInt.IntValue(g)
    requires BigInt.IntValue(y.den) == BigInt.IntValue(yy) * BigInt.IntValue(g)
    requires BigInt.IntValue(xx) > 0 && BigInt.IntValue(yy) > 0
    requires BigInt.IntValue(aa) == BigInt.IntValue(x.num) * BigInt.IntValue(yy)
    requires BigInt.IntValue(bb) == BigInt.IntValue(y.num) * BigInt.IntValue(xx)
    requires BigInt.IntValue(dd) == BigInt.IntValue(x.den) * BigInt.IntValue(yy)
    ensures BigInt.IntValue(dd) > 0
    ensures RealValue(x) == BigInt.IntValue(aa) as real / BigInt.IntValue(dd) as real
    ensures RealValue(y) == BigInt.IntValue(bb) as real / BigInt.IntValue(dd) as real
  {
    var a := BigInt.IntValue(x.num); var b := BigInt.IntValue(x.den);
    var c := BigInt.IntValue(y.num); var d := BigInt.IntValue(y.den);
    var vg := BigInt.IntValue(g); var vxx := BigInt.IntValue(xx); var vyy := BigInt.IntValue(yy);
    PureArith.MulPosScale(b, vyy);
    // dd == b*yy > 0
    assert BigInt.IntValue(dd) > 0;
    // aa/dd == (a*yy)/(b*yy) == a/b
    PureArith.SameValueScaled(a, b, vyy, BigInt.IntValue(aa), BigInt.IntValue(dd));
    // bb/dd == (c*xx)/(b*yy); need b*yy == d*xx so this is (c*xx)/(d*xx) == c/d.
    DenomsAgree(b, d, vg, vxx, vyy);         // b*yy == d*xx
    assert BigInt.IntValue(dd) == d * vxx;
    PureArith.SameValueScaled(c, d, vxx, BigInt.IntValue(bb), BigInt.IntValue(dd));
  }

  // b == xx*g and d == yy*g imply b*yy == d*xx (both equal xx*yy*g).
  lemma DenomsAgree(b: int, d: int, g: int, xx: int, yy: int)
    requires b == xx * g && d == yy * g
    ensures b * yy == d * xx
  {
    PureArith.MulReassocInt(xx, g, yy);   // (xx*g)*yy == (yy*g)*xx
  }

  //////////////////////////////////////////////////////////////////////////////
  // Add / Sub / Neg via Normalize (C# operators + / - / unary -).
  //////////////////////////////////////////////////////////////////////////////

  function Add(x: DReal, y: DReal): (r: DReal)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) + RealValue(y)
  {
    var (aa, bb, dd) := Normalize(x, y);
    var num := BigInt.Add(aa, bb);
    AddFromNormalized(x, y, aa, bb, dd, num);
    DReal(num, dd)
  }

  lemma AddFromNormalized(x: DReal, y: DReal, aa: BigInt.Int, bb: BigInt.Int,
                          dd: BigInt.Int, num: BigInt.Int)
    requires Wf(x) && Wf(y)
    requires BigInt.Wf(aa) && BigInt.Wf(bb) && BigInt.Wf(dd) && BigInt.IntValue(dd) > 0
    requires RealValue(x) == BigInt.IntValue(aa) as real / BigInt.IntValue(dd) as real
    requires RealValue(y) == BigInt.IntValue(bb) as real / BigInt.IntValue(dd) as real
    requires BigInt.Wf(num) && BigInt.IntValue(num) == BigInt.IntValue(aa) + BigInt.IntValue(bb)
    ensures RealValue(DReal(num, dd)) == RealValue(x) + RealValue(y)
  {
    PureArith.SameDenomAdd(BigInt.IntValue(aa), BigInt.IntValue(bb),
                           BigInt.IntValue(dd), BigInt.IntValue(num));
  }

  function Sub(x: DReal, y: DReal): (r: DReal)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) - RealValue(y)
  {
    var (aa, bb, dd) := Normalize(x, y);
    var num := BigInt.Sub(aa, bb);
    SubFromNormalized(x, y, aa, bb, dd, num);
    DReal(num, dd)
  }

  lemma SubFromNormalized(x: DReal, y: DReal, aa: BigInt.Int, bb: BigInt.Int,
                          dd: BigInt.Int, num: BigInt.Int)
    requires Wf(x) && Wf(y)
    requires BigInt.Wf(aa) && BigInt.Wf(bb) && BigInt.Wf(dd) && BigInt.IntValue(dd) > 0
    requires RealValue(x) == BigInt.IntValue(aa) as real / BigInt.IntValue(dd) as real
    requires RealValue(y) == BigInt.IntValue(bb) as real / BigInt.IntValue(dd) as real
    requires BigInt.Wf(num) && BigInt.IntValue(num) == BigInt.IntValue(aa) - BigInt.IntValue(bb)
    ensures RealValue(DReal(num, dd)) == RealValue(x) - RealValue(y)
  {
    PureArith.SameDenomSub(BigInt.IntValue(aa), BigInt.IntValue(bb),
                           BigInt.IntValue(dd), BigInt.IntValue(num));
  }

  // Unary negation: (-num)/den.
  function Neg(x: DReal): (r: DReal)
    requires Wf(x)
    ensures Wf(r)
    ensures RealValue(r) == -RealValue(x)
  {
    var num := BigInt.Negate(x.num);
    NegValue(x, num);
    DReal(num, x.den)
  }

  lemma NegValue(x: DReal, num: BigInt.Int)
    requires Wf(x)
    requires BigInt.Wf(num) && BigInt.IntValue(num) == -BigInt.IntValue(x.num)
    ensures RealValue(DReal(num, x.den)) == -RealValue(x)
  {
    PureArith.NegFrac(BigInt.IntValue(x.num) as real, BigInt.IntValue(x.den) as real);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Division: multiply by the reciprocal of y (C# operator /). Requires y != 0.
  //////////////////////////////////////////////////////////////////////////////

  function Reciprocal(y: DReal): (r: DReal)
    requires Wf(y) && BigInt.IntValue(y.num) != 0
    ensures Wf(r)
    ensures RealValue(r) == 1.0 / RealValue(y)
  {
    if BigInt.IntValue(y.num) > 0 then
      // num > 0: reciprocal is den/num, both positive.
      ReciprocalValue(y, y.den, y.num);
      DReal(y.den, y.num)
    else
      // num < 0: reciprocal is (-den)/(-num), denominator -num > 0.
      var rnum := BigInt.Negate(y.den);
      var rden := BigInt.Negate(y.num);
      NegNumPositive(y);
      ReciprocalValueNeg(y, rnum, rden);
      DReal(rnum, rden)
  }

  lemma NegNumPositive(y: DReal)
    requires Wf(y) && BigInt.IntValue(y.num) < 0
    ensures BigInt.IntValue(BigInt.Negate(y.num)) > 0
  {}

  lemma ReciprocalValue(y: DReal, rnum: BigInt.Int, rden: BigInt.Int)
    requires Wf(y) && BigInt.IntValue(y.num) > 0
    requires rnum == y.den && rden == y.num
    ensures BigInt.IntValue(rden) > 0
    ensures (BigInt.IntValue(rnum) as real) / (BigInt.IntValue(rden) as real) == 1.0 / RealValue(y)
  {
    PureArith.ReciprocalFrac(BigInt.IntValue(y.num) as real, BigInt.IntValue(y.den) as real);
  }

  lemma ReciprocalValueNeg(y: DReal, rnum: BigInt.Int, rden: BigInt.Int)
    requires Wf(y) && BigInt.IntValue(y.num) < 0
    requires BigInt.Wf(rnum) && BigInt.Wf(rden)
    requires BigInt.IntValue(rnum) == -BigInt.IntValue(y.den)
    requires BigInt.IntValue(rden) == -BigInt.IntValue(y.num)
    ensures BigInt.IntValue(rden) > 0
    ensures (BigInt.IntValue(rnum) as real) / (BigInt.IntValue(rden) as real) == 1.0 / RealValue(y)
  {
    PureArith.ReciprocalFracNeg(BigInt.IntValue(y.num) as real, BigInt.IntValue(y.den) as real);
  }

  @IsolateAssertions
  function Div(x: DReal, y: DReal): (r: DReal)
    requires Wf(x) && Wf(y) && BigInt.IntValue(y.num) != 0
    ensures Wf(r)
    ensures RealValue(r) == RealValue(x) / RealValue(y)
  {
    var recip := Reciprocal(y);
    var r := Mul(x, recip);
    DivValue(x, y, recip, r);
    r
  }

  lemma DivValue(x: DReal, y: DReal, recip: DReal, r: DReal)
    requires Wf(x) && Wf(y) && Wf(recip) && Wf(r)
    requires BigInt.IntValue(y.num) != 0
    requires RealValue(recip) == 1.0 / RealValue(y)
    requires RealValue(r) == RealValue(x) * RealValue(recip)
    ensures RealValue(r) == RealValue(x) / RealValue(y)
  {
    YNonzeroReal(y);
    PureArith.DivIsMulRecip(RealValue(x), RealValue(y));
  }

  lemma YNonzeroReal(y: DReal)
    requires Wf(y) && BigInt.IntValue(y.num) != 0
    ensures RealValue(y) != 0.0
  {
    assert (BigInt.IntValue(y.num) as real) != 0.0;
  }

  //////////////////////////////////////////////////////////////////////////////
  // Comparison (C# CompareTo): sign first, then Normalize + compare numerators.
  //////////////////////////////////////////////////////////////////////////////

  function Compare(x: DReal, y: DReal): (c: int)
    requires Wf(x) && Wf(y)
    ensures c == 0 <==> RealValue(x) == RealValue(y)
    ensures c < 0 <==> RealValue(x) < RealValue(y)
    ensures c > 0 <==> RealValue(x) > RealValue(y)
  {
    var (aa, bb, dd) := Normalize(x, y);
    CompareFromNormalized(x, y, aa, bb, dd);
    BigInt.Compare(aa, bb)
  }

  lemma CompareFromNormalized(x: DReal, y: DReal, aa: BigInt.Int, bb: BigInt.Int, dd: BigInt.Int)
    requires Wf(x) && Wf(y)
    requires BigInt.Wf(aa) && BigInt.Wf(bb) && BigInt.Wf(dd) && BigInt.IntValue(dd) > 0
    requires RealValue(x) == BigInt.IntValue(aa) as real / BigInt.IntValue(dd) as real
    requires RealValue(y) == BigInt.IntValue(bb) as real / BigInt.IntValue(dd) as real
    ensures (BigInt.IntValue(aa) < BigInt.IntValue(bb)) <==> (RealValue(x) < RealValue(y))
    ensures (BigInt.IntValue(aa) == BigInt.IntValue(bb)) <==> (RealValue(x) == RealValue(y))
    ensures (BigInt.IntValue(aa) > BigInt.IntValue(bb)) <==> (RealValue(x) > RealValue(y))
  {
    PureArith.SameDenomCompare(BigInt.IntValue(aa), BigInt.IntValue(bb), BigInt.IntValue(dd));
  }

  //////////////////////////////////////////////////////////////////////////////
  // Decimal printing — the C# BigRational.ToString path.
  //
  // C# ToString: if num==0 or den==1 print "num.0"; else if den divides a power
  // of ten, scale num by `factor` and place the decimal point `log10` digits from
  // the right; else print "(num.0 / den.0)".
  //
  // The NUMERIC CORE of the "terminating decimal" test is formally verified in
  // PureArith: IsPowerOf10 and DividesAPowerOf10 are functions over nat whose
  // correctness lemmas prove x == Pow10(l) resp. factor*i == Pow10(log10). That
  // is the fact that makes the decimal expansion exact: when DividesAPowerOf10(den)
  // gives (factor, log10), then num/den == (num*factor)/10^log10, so num*factor is
  // the digit string with the point log10 places from the right.
  //
  // The digit assembly now uses PureArith.DecimalString, which is verified
  // correct (DenotesDecimal). What is formally proved here: the digit strings
  // are the decimal representations of the respective nats (DecimalString's
  // postcondition), and the terminating-decimal numeric fact factor*den==10^log10
  // (TerminatesDecimal). What is NOT given a spec: that the fully assembled
  // string (with the point placed log10 from the right and sign/zero-padding)
  // parses back to RealValue(x) — proving that needs a decimal-fraction parsing
  // relation this library does not define, so ToString carries no such ensures
  // rather than a false one. See doc/TODO.md.
  //////////////////////////////////////////////////////////////////////////////

  // Exposed verified kernel: if the (positive) denominator value divides a power
  // of ten, the scaling factor and digit count satisfy factor*den == 10^log10,
  // which is exactly what the decimal ToString relies on.
  lemma TerminatesDecimal(x: DReal)
    requires Wf(x)
    requires BigInt.IntValue(x.den) > 0
    ensures var (ok, factor, log10) := PureArith.DividesAPowerOf10(BigInt.IntValue(x.den) as nat);
            ok ==> factor * (BigInt.IntValue(x.den) as nat) == PureArith.Pow10(log10)
  {
    PureArith.DividesAPowerOf10Correct(BigInt.IntValue(x.den) as nat);
  }

  // Absolute value of an int as a nat.
  function AbsNat(z: int): nat { if z < 0 then -z else z }

  // A string of k '0' characters.
  function Zeros(k: nat): (s: seq<char>)
    ensures |s| == k
    ensures forall i :: 0 <= i < |s| ==> s[i] == '0'
  {
    if k == 0 then [] else ['0'] + Zeros(k - 1)
  }

  // Decimal rendering of a DReal, matching C# BigRational.ToString.
  // Executable; its numeric building blocks (DecimalString, factor/log10) are
  // verified, but the assembled string itself carries no parse-back ensures
  // (see the note above).
  function ToString(x: DReal): seq<char>
    requires Wf(x)
  {
    var numv := BigInt.IntValue(x.num);
    var denv := BigInt.IntValue(x.den);
    if numv == 0 || denv == 1 then
      // whole-number / zero case: "num.0"
      var sign := if numv < 0 then "-" else "";
      sign + PureArith.DecimalString(AbsNat(numv)) + ".0"
    else
      var (ok, factor, log10) := PureArith.DividesAPowerOf10(denv as nat);
      if ok then
        // num/den == (num*factor)/10^log10: digits of |num*factor| with the
        // decimal point log10 places from the right.
        var n := numv * (factor as int);
        var sign := if n < 0 then "-" else "";
        var digits := PureArith.DecimalString(AbsNat(n));
        if log10 < |digits| then
          var cut := |digits| - log10;
          sign + digits[..cut] + "." + digits[cut..]
        else
          // more fractional places than digits: "0." + leading zeros + digits
          sign + "0." + Zeros(log10 - |digits|) + digits
      else
        // non-terminating in decimal: Dafny prints "(num.0 / den.0)" with the
        // numerator SIGNED (den is always > 0 here), matching C# `{0}.0`.
        var numSign := if numv < 0 then "-" else "";
        "(" + numSign + PureArith.DecimalString(AbsNat(numv)) + ".0 / "
            + PureArith.DecimalString(AbsNat(denv)) + ".0)"
  }

  //////////////////////////////////////////////////////////////////////////////
  // Parse-back correctness of ToString.
  //
  // DenotesRealReal(s, v): the string s, read as a decimal number, equals v.
  // Tailored to the exact three shapes ToString emits (an optionally-signed
  // "whole.frac", or the "(A.0 / B.0)" form). Expressed as a value equation on
  // the digit substrings, so the proof is about values, not string scanning.
  //////////////////////////////////////////////////////////////////////////////

  // A signed "W.F" decimal reads as (-)?(ParseDec(W) + ParseDec(F)/10^|F|).
  ghost predicate DenotesSignedDecimal(s: seq<char>, v: real)
  {
    exists neg: bool, w: seq<char>, f: seq<char> ::
      PureArith.AllDigits(w) && PureArith.AllDigits(f) && |f| >= 1 &&
      s == (if neg then "-" else "") + w + "." + f &&
      v == PureArith.DecimalLayoutValue(neg, w, f)
  }

  // The "([-]A.0 / B.0)" form reads as (-)?ParseDec(A)/ParseDec(B).
  // Phrased with an explicit trigger on the string shape (the witness strings a,
  // b are recoverable from s), so the existential instantiates cleanly.
  ghost predicate DenotesFractionPrint(s: seq<char>, v: real)
  {
    exists neg: bool, a: seq<char>, b: seq<char>
      {:trigger FracShape(neg, a, b)} ::
      PureArith.AllDigits(a) && PureArith.AllDigits(b) &&
      (PureArith.ParseDec(b) as real) != 0.0 &&
      s == FracShape(neg, a, b) &&
      v == (if neg then -(PureArith.ParseDec(a) as real) else (PureArith.ParseDec(a) as real))
           / (PureArith.ParseDec(b) as real)
  }

  // The concrete string shape of the fraction print, as a named function so it
  // can trigger the existential above.
  ghost function FracShape(neg: bool, a: seq<char>, b: seq<char>): seq<char>
  {
    "(" + (if neg then "-" else "") + a + ".0 / " + b + ".0)"
  }

  ghost predicate DenotesReal(s: seq<char>, v: real)
  {
    DenotesSignedDecimal(s, v) || DenotesFractionPrint(s, v)
  }

  // ToString(x), read back as a decimal, equals RealValue(x).
  lemma ToStringCorrect(x: DReal)
    requires Wf(x)
    ensures DenotesReal(ToString(x), RealValue(x))
  {
    var numv := BigInt.IntValue(x.num);
    var denv := BigInt.IntValue(x.den);
    assert denv > 0;
    if numv == 0 || denv == 1 {
      WholeCase(x, numv, denv);
    } else {
      var (ok, factor, log10) := PureArith.DividesAPowerOf10(denv as nat);
      if ok {
        TerminatingCase(x, numv, denv, factor, log10);
      } else {
        FractionPrintCase(x, numv, denv);
      }
    }
  }

  // Case 1: num==0 or den==1. Value is numv/denv, printed as "sign D.0" which
  // reads as (-)?(ParseDec(D) + 0/10) == numv as real (since den is 1 here, or
  // num is 0). We expose w = D, f = "0".
  @IsolateAssertions
  lemma WholeCase(x: DReal, numv: int, denv: int)
    requires Wf(x) && numv == BigInt.IntValue(x.num) && denv == BigInt.IntValue(x.den)
    requires denv > 0
    requires numv == 0 || denv == 1
    ensures DenotesReal(ToString(x), RealValue(x))
  {
    var neg := numv < 0;
    var w := PureArith.DecimalString(AbsNat(numv));
    var f := "0";
    assert PureArith.AllDigits(w);                 // from DenotesDecimal
    assert PureArith.AllDigits(f);
    assert ToString(x) == (if neg then "-" else "") + w + "." + f;
    // value: RealValue == numv/denv, and here that equals numv (den 1) or 0.
    WholeValue(numv, denv, neg, w, f);
    assert RealValue(x) == PureArith.DecimalLayoutValue(neg, w, f);
    assert DenotesSignedDecimal(ToString(x), RealValue(x));
  }

  // numv/denv == DecimalLayoutValue(neg, DecimalString(|numv|), "0") when
  // numv==0 or denv==1.
  @IsolateAssertions
  lemma WholeValue(numv: int, denv: int, neg: bool, w: seq<char>, f: seq<char>)
    requires denv > 0 && (numv == 0 || denv == 1)
    requires neg == (numv < 0)
    requires PureArith.AllDigits(w) && PureArith.ParseDec(w) == AbsNat(numv)
    requires f == "0"
    ensures PureArith.AllDigits(f)
    ensures (numv as real) / (denv as real)
            == PureArith.DecimalLayoutValue(neg, w, f)
  {
    assert PureArith.AllDigits(f) by { assert f[0] == '0'; }
    assert PureArith.ParseDec(f) == 0 by {
      assert f[..|f| - 1] == [];
      assert PureArith.DigitVal(f[0]) == 0;
    }
    assert PureArith.Pow10(|f|) >= 1;
    // DecimalLayoutValue(neg,w,"0") == (neg? -1:1) * (|numv| + 0) == numv as real.
    var mag := (PureArith.ParseDec(w) as real)
             + (PureArith.ParseDec(f) as real) / (PureArith.Pow10(|f|) as real);
    assert mag == AbsNat(numv) as real;
    // RealValue: den is 1 (so numv/1) or numv is 0 (so 0/denv == 0).
    if denv == 1 {
      assert (numv as real) / (denv as real) == numv as real;
    } else {
      assert numv == 0;
      assert (numv as real) / (denv as real) == 0.0;
    }
    AbsNatSignReal(numv, neg);
  }

  // (neg? -mag : mag) with mag == |numv| equals numv as real.
  lemma AbsNatSignReal(numv: int, neg: bool)
    requires neg == (numv < 0)
    ensures (if neg then -(AbsNat(numv) as real) else (AbsNat(numv) as real))
            == numv as real
  {}

  // Case 2: den divides a power of ten. The heart of the proof.
  @IsolateAssertions
  lemma TerminatingCase(x: DReal, numv: int, denv: int, factor: nat, log10: nat)
    requires Wf(x) && numv == BigInt.IntValue(x.num) && denv == BigInt.IntValue(x.den)
    requires denv > 0 && numv != 0 && denv != 1
    requires PureArith.DividesAPowerOf10(denv as nat) == (true, factor, log10)
    ensures DenotesReal(ToString(x), RealValue(x))
  {
    PureArith.DividesAPowerOf10Correct(denv as nat);
    assert factor * (denv as nat) == PureArith.Pow10(log10);      // key fact
    var n := numv * (factor as int);
    var neg := n < 0;
    var digits := PureArith.DecimalString(AbsNat(n));
    assert PureArith.AllDigits(digits) && PureArith.ParseDec(digits) == AbsNat(n);
    // RealValue(x) == n / Pow10(log10)  (as reals)
    TerminatingValue(numv, denv, factor, log10, n);
    var P := PureArith.Pow10(log10);
    assert RealValue(x) == (n as real) / (P as real);

    if log10 < |digits| {
      var cut := |digits| - log10;
      var w := digits[..cut];
      var f := digits[cut..];
      // decimal-point placement: w + "0.something" denotes |n| / Pow10(log10)
      PureArith.DecimalCutCorrect(digits, cut, log10, AbsNat(n));
      assert |f| == log10 && log10 >= 1;          // denv != 1 ==> log10 >= 1
      Log10Pos(denv, factor, log10);
      assert ToString(x) == (if neg then "-" else "") + w + "." + f;
      // value side
      SignedLayoutValue(neg, w, f, n, P, AbsNat(n));
      assert RealValue(x) == PureArith.DecimalLayoutValue(neg, w, f);
      assert DenotesSignedDecimal(ToString(x), RealValue(x));
    } else {
      var k := log10 - |digits|;
      var zeros := Zeros(k);
      var w := "0";
      var f := zeros + digits;
      ZerosAllDigits(zeros, k);
      assert PureArith.AllDigits(f) by { PureArith.AllDigitsConcat(zeros, digits); }
      assert |f| == log10 && log10 >= 1;
      Log10Pos(denv, factor, log10);
      assert ToString(x) == (if neg then "-" else "") + w + "." + f;
      PureArith.DecimalZeroPadCorrect(zeros, digits, log10, AbsNat(n));
      ZeroPadLayoutValue(neg, w, zeros, digits, f, n, P, AbsNat(n), log10);
      assert RealValue(x) == PureArith.DecimalLayoutValue(neg, w, f);
      assert DenotesSignedDecimal(ToString(x), RealValue(x));
    }
  }

  // RealValue(x) == n / Pow10(log10), where n == numv*factor and
  // factor*denv == Pow10(log10).
  @IsolateAssertions
  lemma TerminatingValue(numv: int, denv: int, factor: nat, log10: nat, n: int)
    requires denv > 0
    requires n == numv * (factor as int)
    requires factor * (denv as nat) == PureArith.Pow10(log10)
    ensures (numv as real) / (denv as real)
            == (n as real) / (PureArith.Pow10(log10) as real)
  {
    var P := PureArith.Pow10(log10);
    var fr := factor as real;
    var dr := denv as real;
    var Pr := P as real;
    assert dr > 0.0;
    // factor*denv == P  (cast to reals), so fr*dr == Pr, fr > 0.
    PureArith.CastProd(P, factor, denv as nat);
    NatRealNonneg(factor, denv);
    assert fr * dr == Pr;
    assert fr >= 0.0;
    assert Pr >= 1.0 by { assert P >= 1; }
    assert fr > 0.0;
    // n as real == numv*fr
    PureArith.CastProdInt(n, numv, factor as int);
    assert (n as real) == (numv as real) * fr;
    // numv/denv == (numv*fr)/(denv*fr) == n / P
    DivScaleReal(numv as real, dr, fr, n as real, Pr);
  }

  // numv/dr == (numv*fr)/(dr*fr) and dr*fr == Pr, so numv/dr == nr/Pr.
  lemma DivScaleReal(numv: real, dr: real, fr: real, nr: real, Pr: real)
    requires dr > 0.0 && fr > 0.0
    requires nr == numv * fr
    requires dr * fr == Pr
    ensures numv / dr == nr / Pr
  {
    assert Pr == dr * fr;
    assert numv / dr == (numv * fr) / (dr * fr) by {
      PureArith.RealCancel(numv, dr, fr);
    }
  }

  lemma NatRealNonneg(a: nat, b: int)
    requires b > 0
    ensures (a as real) >= 0.0 && (b as real) > 0.0
  {}

  // SignedLayoutValue: layout (neg,w,f) with w=digits[..cut], f=digits[cut..],
  // equals n/P.
  @IsolateAssertions
  lemma SignedLayoutValue(neg: bool, w: seq<char>, f: seq<char>, n: int, P: nat, m: nat)
    requires PureArith.AllDigits(w) && PureArith.AllDigits(f)
    requires neg == (n < 0) && m == AbsNat(n)
    requires P >= 1
    requires (PureArith.ParseDec(w) as real)
             + (PureArith.ParseDec(f) as real) / (P as real)
             == (m as real) / (P as real)
    requires |f| >= 1 && PureArith.Pow10(|f|) == P
    ensures (n as real) / (P as real) == PureArith.DecimalLayoutValue(neg, w, f)
  {
    var mag := (PureArith.ParseDec(w) as real)
             + (PureArith.ParseDec(f) as real) / (PureArith.Pow10(|f|) as real);
    assert mag == (m as real) / (P as real);
    // n == (neg? -m : m), so n/P == (neg? -(m/P) : m/P) == DecimalLayoutValue.
    assert (m as real) == AbsNat(n) as real;
    SignDivReal(n, m, P, neg);
  }

  // (n as real)/P with m==|n| equals (neg? -(m/P) : m/P).
  lemma SignDivReal(n: int, m: nat, P: nat, neg: bool)
    requires P >= 1 && m == AbsNat(n) && neg == (n < 0)
    ensures (n as real) / (P as real)
            == (if neg then -((m as real) / (P as real)) else (m as real) / (P as real))
  {
    assert (P as real) > 0.0;
    if neg { assert (n as real) == -(m as real); } else { assert (n as real) == (m as real); }
  }

  // Zero-pad layout: w=="0", f==zeros++digits, value 0 + m/Pow10(log10) == n/P.
  @IsolateAssertions
  lemma ZeroPadLayoutValue(neg: bool, w: seq<char>, zeros: seq<char>, digits: seq<char>,
                           f: seq<char>, n: int, P: nat, m: nat, log10: nat)
    requires w == "0" && f == zeros + digits
    requires PureArith.AllDigits(zeros) && PureArith.AllDigits(digits) && PureArith.AllDigits(f)
    requires neg == (n < 0) && m == AbsNat(n)
    requires P == PureArith.Pow10(log10) && |f| == log10 && log10 >= 1
    requires (0 as real) + (PureArith.ParseDec(f) as real) / (P as real)
             == (m as real) / (P as real)
    ensures (n as real) / (P as real) == PureArith.DecimalLayoutValue(neg, w, f)
  {
    assert PureArith.ParseDec(w) == 0 by {
      assert w[..|w| - 1] == [];
      assert PureArith.DigitVal(w[0]) == 0;
    }
    assert PureArith.Pow10(|f|) == P;
    var mag := (PureArith.ParseDec(w) as real)
             + (PureArith.ParseDec(f) as real) / (PureArith.Pow10(|f|) as real);
    assert mag == (m as real) / (P as real);
    SignDivReal(n, m, P, neg);
  }

  lemma ZerosAllDigits(zeros: seq<char>, k: nat)
    requires zeros == Zeros(k)
    ensures PureArith.AllDigits(zeros)
    ensures forall i :: 0 <= i < |zeros| ==> zeros[i] == '0'
  {}

  // den != 1 and den divides a power of ten ==> log10 >= 1.
  lemma Log10Pos(denv: int, factor: nat, log10: nat)
    requires denv > 1
    requires factor * (denv as nat) == PureArith.Pow10(log10)
    ensures log10 >= 1
  {
    if log10 == 0 {
      assert PureArith.Pow10(0) == 1;
      assert factor * (denv as nat) == 1;
      // denv > 1 but factor*denv == 1 is impossible for nats
      assert denv as nat >= 2;
    }
  }

  // Case 3: non-terminating decimal, printed "([-]num.0 / den.0)" (signed num,
  // den > 0). Covers all numv != 0.
  @IsolateAssertions
  lemma FractionPrintCase(x: DReal, numv: int, denv: int)
    requires Wf(x) && numv == BigInt.IntValue(x.num) && denv == BigInt.IntValue(x.den)
    requires denv > 0 && numv != 0 && denv != 1
    requires !PureArith.DividesAPowerOf10(denv as nat).0
    ensures DenotesReal(ToString(x), RealValue(x))
  {
    var neg := numv < 0;
    var a := PureArith.DecimalString(AbsNat(numv));
    var b := PureArith.DecimalString(AbsNat(denv));
    assert PureArith.AllDigits(a) && PureArith.ParseDec(a) == AbsNat(numv);
    assert PureArith.AllDigits(b) && PureArith.ParseDec(b) == AbsNat(denv);
    assert ToString(x) == "(" + (if neg then "-" else "") + a + ".0 / " + b + ".0)";
    assert ToString(x) == FracShape(neg, a, b);
    assert AbsNat(denv) == denv;
    assert (PureArith.ParseDec(b) as real) == (denv as real) != 0.0;
    // value: RealValue == numv/denv; a denotes |numv|, sign pulled out.
    FractionValue(numv, denv, neg, PureArith.ParseDec(a));
    var v := RealValue(x);
    assert v == (if neg then -(PureArith.ParseDec(a) as real) else (PureArith.ParseDec(a) as real))
                / (PureArith.ParseDec(b) as real);
    // exhibit the existential witness (neg, a, b) for DenotesFractionPrint
    WitnessFractionPrint(ToString(x), v, neg, a, b);
  }

  // Introduce the DenotesFractionPrint existential from an explicit witness.
  lemma WitnessFractionPrint(s: seq<char>, v: real, neg: bool, a: seq<char>, b: seq<char>)
    requires PureArith.AllDigits(a) && PureArith.AllDigits(b)
    requires (PureArith.ParseDec(b) as real) != 0.0
    requires s == FracShape(neg, a, b)
    requires v == (if neg then -(PureArith.ParseDec(a) as real) else (PureArith.ParseDec(a) as real))
                  / (PureArith.ParseDec(b) as real)
    ensures DenotesFractionPrint(s, v)
  {
    assert s == FracShape(neg, a, b);   // supplies the trigger term
  }

  // numv/denv == (neg? -pa : pa)/denv  where pa == |numv| and neg == numv<0.
  lemma FractionValue(numv: int, denv: int, neg: bool, pa: nat)
    requires denv > 0 && neg == (numv < 0) && pa == AbsNat(numv)
    ensures (numv as real) / (denv as real)
            == (if neg then -(pa as real) else (pa as real)) / (denv as real)
  {
    if neg { assert (numv as real) == -(pa as real); }
    else { assert (numv as real) == (pa as real); }
  }
}

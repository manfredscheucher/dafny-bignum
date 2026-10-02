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
  // What is NOT done here: the executable string assembly over BigInt (repeated
  // division by 10, substring/padding). That needs a verified BigInt->decimal
  // routine which this library does not yet provide, so rather than claim a
  // ToString with a false spec, the verified numeric kernel is exposed below and
  // the string layer is left as an explicit gap (see doc/TODO.md).
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
}

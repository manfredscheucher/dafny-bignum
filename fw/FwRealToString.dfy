/*******************************************************************************
 * dafny-bignum / fixed-width: FwRealToString
 *
 * Decimal rendering of FwReal, modelling Dafny BigRational.ToString.
 *
 * VERIFIED (Gate 1): the digit machinery is fixed-width and proven — `DigitsOf`
 * extracts the decimal digits of a limb magnitude by repeated FwDivMod.DivMod by
 * [10] (NOT nat division), the digit char is a constant-string index by the
 * remainder limb, lengths are sequence lengths, and the result is proven to
 * denote Value(mag) via ParseDec. On top of that, `ToString` carries a proven
 * parse-back: `ensures DenotesReal(ToString(x), RealValue(x))`, i.e. the printed
 * string, read back as a decimal, equals the real value. BOTH shapes it emits
 * are covered: the whole-number form "[-]D.0" (DenotesSignedDecimal) and the
 * exact-fraction form "([-]A.0 / B.0)" (DenotesFractionPrint). There is no
 * terminating-decimal (point-placement) case here — fw never emits one — so,
 * unlike src/DafnyReal.dfy, only the WholeCase and FractionPrintCase are ported.
 * No int/nat in compiled code, no false ensures (the parse-back spec is ghost).
 *
 * C++-translatable (Gate 2): YES, Boost-free (0 translate errors). One subtlety:
 * the C++ backend does NOT compile a `seq<char>` *display* built from a char
 * variable (`[dc]`), but it DOES compile a substring of a string literal. So the
 * single digit is emitted as `DIGITS[dlimb..dlimb+1]` (provably `[dc]`), and the
 * whole module translates cleanly. Kept separate from FwReal.dfy only for tidy
 * layering, not because of any C++ limitation.
 *******************************************************************************/

include "FwNat.dfy"
include "FwInt.dfy"
include "FwCompare.dfy"
include "FwDivMod.dfy"
include "FwReal.dfy"
include "FwRealPrint.dfy"

module FwRealToString {
  import opened FwNat
  import FwInt
  import opened FwCompare
  import FwDivMod
  import opened FwReal
  import FwRealPrint

  const DIGITS: seq<char> := "0123456789"

  //////////////////////////////////////////////////////////////////////////////
  // Parse-back semantics of the printed string (GHOST). Ported from
  // src/DafnyReal.dfy (DenotesSignedDecimal / DenotesFractionPrint / DenotesReal),
  // trimmed to the two shapes fw's ToString actually emits:
  //   (a) "[-]W.0"             (whole-number case; fraction part is always "0")
  //   (b) "([-]A.0 / B.0)"     (exact-fraction print)
  // There is NO terminating-decimal (point placement) case in fw, so only the
  // WholeCase and FractionPrintCase of the src proof are ported.
  // These are ghost specs, so int/nat/real are fine (no fixed-width constraint).
  //////////////////////////////////////////////////////////////////////////////

  ghost function Pow10(n: nat): (r: nat)
    ensures r >= 1
  {
    if n == 0 then 1 else 10 * Pow10(n - 1)
  }

  // Value of a signed "W.F" decimal: (-)?(ParseDec(W) + ParseDec(F)/10^|F|).
  ghost function DecimalLayoutValue(neg: bool, w: seq<char>, f: seq<char>): real
    requires FwRealPrint.AllDigits(w) && FwRealPrint.AllDigits(f)
  {
    var mag := (FwRealPrint.ParseDec(w) as real)
             + (FwRealPrint.ParseDec(f) as real) / (Pow10(|f|) as real);
    if neg then -mag else mag
  }

  // A signed "W.F" decimal reads as (-)?(ParseDec(W) + ParseDec(F)/10^|F|).
  ghost predicate DenotesSignedDecimal(s: seq<char>, v: real)
  {
    exists neg: bool, w: seq<char>, f: seq<char> ::
      FwRealPrint.AllDigits(w) && FwRealPrint.AllDigits(f) && |f| >= 1 &&
      s == (if neg then "-" else "") + w + "." + f &&
      v == DecimalLayoutValue(neg, w, f)
  }

  // The concrete string shape of the fraction print, as a named function so it
  // can trigger the existential in DenotesFractionPrint.
  ghost function FracShape(neg: bool, a: seq<char>, b: seq<char>): seq<char>
  {
    "(" + (if neg then "-" else "") + a + ".0 / " + b + ".0)"
  }

  // The "([-]A.0 / B.0)" form reads as (-)?ParseDec(A)/ParseDec(B). (The ".0"
  // suffixes are decorative: A.0 == A as an integer.)
  ghost predicate DenotesFractionPrint(s: seq<char>, v: real)
  {
    exists neg: bool, a: seq<char>, b: seq<char>
      {:trigger FracShape(neg, a, b)} ::
      FwRealPrint.AllDigits(a) && FwRealPrint.AllDigits(b) &&
      (FwRealPrint.ParseDec(b) as real) != 0.0 &&
      s == FracShape(neg, a, b) &&
      v == (if neg then -(FwRealPrint.ParseDec(a) as real) else (FwRealPrint.ParseDec(a) as real))
           / (FwRealPrint.ParseDec(b) as real)
  }

  ghost predicate DenotesReal(s: seq<char>, v: real)
  {
    DenotesSignedDecimal(s, v) || DenotesFractionPrint(s, v)
  }

  lemma TenValue()
    ensures Value([10 as limb]) == 10 && Normalized([10 as limb])
  {
  }

  // Decimal digits of a magnitude, most-significant first, via repeated division
  // by ten. Proven to denote Value(mag). Recurses on the (ghost) Value, which
  // strictly decreases because quotient-by-ten shrinks a value >= 10.
  method DigitsOf(mag: seq<limb>) returns (s: seq<char>)
    requires Normalized(mag)
    ensures |s| >= 1
    ensures FwRealPrint.AllDigits(s)
    ensures FwRealPrint.ParseDec(s) == Value(mag)
    decreases Value(mag)
  {
    TenValue();
    var ten: seq<limb> := [10 as limb];
    var q, r := FwDivMod.DivMod(mag, ten);
    var dlimb: limb;
    if |r| == 0 {
      dlimb := 0;
      assert Value(r) == 0;
    } else {
      dlimb := r[0];
      RSingleDigit(r);
    }
    var dc := DIGITS[dlimb];
    DigitCharFacts(dlimb, dc);
    // Use a substring of the DIGITS literal rather than the char display [dc]:
    // the C++ backend compiles literal-substrings but not `seq<char>` displays
    // built from a char variable. DIGITS[dlimb..dlimb+1] is provably [dc].
    DigitsLow(dlimb);                       // dlimb < 10, so the slice is valid
    var dcs := DIGITS[dlimb..dlimb + 1];
    assert dcs == [dc];

    if |q| == 0 {
      assert Value(q) == 0;
      QZeroSmall(mag, q, r);
      s := dcs;
      FwRealPrint.ParseDecSingle(dc);
    } else {
      QuotientDecreases(mag, q, r);
      var hi := DigitsOf(q);
      DigitsStep(mag, q, r, hi, dc);
      s := hi + dcs;
    }
  }

  // The remainder digit is < 10, so DIGITS[dlimb..dlimb+1] is in range.
  lemma DigitsLow(dlimb: limb)
    requires (dlimb as nat) < 10
    ensures (dlimb as nat) + 1 <= |DIGITS|
  {}

  lemma QuotientDecreases(mag: seq<limb>, q: seq<limb>, r: seq<limb>)
    requires Normalized(q) && q != []
    requires Value(mag) == Value(q) * Value([10 as limb]) + Value(r)
    requires Value([10 as limb]) == 10
    ensures Value(q) < Value(mag)
  {
    FwInt.NonEmptyMagPositive(q);
    assert Value(q) * 10 >= Value(q) + Value(q) * 9;
    assert Value(q) * 9 >= 9;
  }

  lemma RSingleDigit(r: seq<limb>)
    requires Normalized(r) && r != [] && Value(r) < 10
    ensures |r| == 1
    ensures Value(r) == (r[0] as nat)
    ensures (r[0] as nat) < 10
  {
    if |r| >= 2 {
      FwCompare.TopLimbLowerBound(r);
      Pow32Positive(|r| - 1);
      assert Value(r) >= Pow32(|r| - 1);
      Pow32Big(|r| - 1);
    }
    assert Value(r) == (r[0] as nat) + 0x1_0000_0000 * Value(r[1..]);
    assert r[1..] == [];
  }

  lemma Pow32Big(k: nat)
    requires k >= 1
    ensures Pow32(k) >= 0x1_0000_0000
  {
    Pow32Positive(k - 1);
    assert Pow32(k) == 0x1_0000_0000 * Pow32(k - 1);
  }

  lemma DigitCharFacts(d: limb, c: char)
    requires d < 10
    requires c == DIGITS[d]
    ensures FwRealPrint.IsDigitChar(c)
    ensures FwRealPrint.DigitVal(c) == (d as nat)
  {
    assert DIGITS[d] == FwRealPrint.DigitChar(d as nat);
    FwRealPrint.DigitRoundTrip(d as nat);
  }

  lemma QZeroSmall(mag: seq<limb>, q: seq<limb>, r: seq<limb>)
    requires Value(q) == 0
    requires Value(mag) == Value(q) * Value([10 as limb]) + Value(r)
    requires Value(r) < 10
    ensures Value(mag) == Value(r)
    ensures Value(mag) < 10
  {
  }

  lemma DigitsStep(mag: seq<limb>, q: seq<limb>, r: seq<limb>,
                   hi: seq<char>, dc: char)
    requires FwRealPrint.AllDigits(hi) && FwRealPrint.ParseDec(hi) == Value(q)
    requires FwRealPrint.IsDigitChar(dc)
    requires Value(mag) == Value(q) * Value([10 as limb]) + Value(r)
    requires Value([10 as limb]) == 10
    requires FwRealPrint.DigitVal(dc) == Value(r)
    ensures FwRealPrint.AllDigits(hi + [dc])
    ensures FwRealPrint.ParseDec(hi + [dc]) == Value(mag)
  {
    var s := hi + [dc];
    assert s[..|s| - 1] == hi;
    assert s[|s| - 1] == dc;
    assert FwRealPrint.AllDigits(s);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Parse-back correctness helpers (GHOST), ported from the WholeCase /
  // FractionPrintCase of src/DafnyReal.dfy's ToStringCorrect.
  //////////////////////////////////////////////////////////////////////////////

  // "0" is a one-digit string denoting 0.
  lemma ZeroDigitString()
    ensures FwRealPrint.AllDigits("0") && FwRealPrint.ParseDec("0") == 0
  {
    assert "0"[..0] == [];
    assert FwRealPrint.DigitVal("0"[0]) == 0;
  }

  // For a well-formed FwInt, IntValue sign is determined by the negative flag:
  // IntValue(x) == (neg? -Value(mag) : Value(mag)), and Wf gives no "-0".
  lemma IntValueAbs(n: FwInt.Int)
    requires FwInt.Wf(n)
    ensures FwInt.IntValue(n)
            == (if n.negative then -(Value(n.mag) as int) else Value(n.mag) as int)
  {}

  // Whole-number case value: RealValue(x) == DecimalLayoutValue(neg, w, "0"),
  // where w denotes Value(numMag), neg == x.num.negative, and either numMag is
  // empty (value 0) or den's value is 1.
  @IsolateAssertions
  lemma WholeValue(x: Real, w: seq<char>, neg: bool)
    requires Wf(x)
    requires FwRealPrint.AllDigits(w)
    requires FwRealPrint.ParseDec(w) == Value(x.num.mag)
    requires neg == x.num.negative
    requires |x.num.mag| == 0 || FwInt.IntValue(x.den) == 1
    ensures RealValue(x) == DecimalLayoutValue(neg, w, "0")
  {
    ZeroDigitString();
    // mag side: ParseDec(w) + ParseDec("0")/10 == Value(numMag).
    assert FwRealPrint.ParseDec("0") == 0;
    assert Pow10(1) == 10;
    var mag := (FwRealPrint.ParseDec(w) as real)
             + (FwRealPrint.ParseDec("0") as real) / (Pow10(|"0"|) as real);
    assert |"0"| == 1;
    assert mag == Value(x.num.mag) as real;
    // RealValue == IntValue(num)/IntValue(den); den>0.
    var numv := FwInt.IntValue(x.num);
    var denv := FwInt.IntValue(x.den);
    assert denv > 0;
    IntValueAbs(x.num);
    if |x.num.mag| == 0 {
      // numv == 0, so RealValue == 0 == DecimalLayoutValue (mag part 0).
      assert Value(x.num.mag) == 0;
      assert numv == 0;
      assert RealValue(x) == 0.0;
      assert mag == 0.0;
    } else {
      // den value is 1, so RealValue == numv.
      assert denv == 1;
      assert RealValue(x) == (numv as real) / (1 as real) == numv as real;
    }
    // DecimalLayoutValue(neg,w,"0") == (neg? -mag : mag) == numv as real.
    if neg {
      assert numv == -(Value(x.num.mag) as int);
      assert DecimalLayoutValue(neg, w, "0") == -mag;
    } else {
      assert numv == Value(x.num.mag) as int;
      assert DecimalLayoutValue(neg, w, "0") == mag;
    }
  }

  // Fraction-print case value: RealValue(x) == (neg? -pa : pa)/pb, where
  // pa == Value(numMag) == |IntValue(num)|, pb == Value(denMag) == IntValue(den),
  // neg == x.num.negative.
  @IsolateAssertions
  lemma FractionValue(x: Real, pa: nat, pb: nat, neg: bool)
    requires Wf(x)
    requires pa == Value(x.num.mag) && pb == Value(x.den.mag)
    requires neg == x.num.negative
    ensures (pb as real) != 0.0
    ensures RealValue(x)
            == (if neg then -(pa as real) else (pa as real)) / (pb as real)
  {
    var numv := FwInt.IntValue(x.num);
    var denv := FwInt.IntValue(x.den);
    assert denv > 0;
    IntValueAbs(x.num);
    IntValueAbs(x.den);
    // den is positive, so not negative; IntValue(den) == Value(denMag) == pb.
    assert denv == pb as int;
    assert (pb as real) != 0.0;
    // numv == (neg? -pa : pa).
    if neg {
      assert numv == -(pa as int);
      assert (numv as real) == -(pa as real);
    } else {
      assert numv == pa as int;
      assert (numv as real) == pa as real;
    }
    assert RealValue(x) == (numv as real) / (denv as real);
  }

  // ToString: the whole-number case prints "sign D.0"; otherwise the exact
  // value as Dafny's "(num.0 / den.0)" form. Digits via the verified DigitsOf.
  // (Not the terminating-decimal point placement — that is proven in src/; here
  // the exact fraction form is always a faithful rendering.) The result is
  // proven to parse back to RealValue(x) (DenotesReal), covering both shapes.
  @IsolateAssertions
  method ToString(x: Real) returns (s: seq<char>)
    requires Wf(x)
    ensures DenotesReal(s, RealValue(x))
  {
    var numMag := x.num.mag;
    var sign: seq<char> := if x.num.negative then "-" else "";
    var one: seq<limb> := [1 as limb];
    TenValue();
    var denIsOne := FwCompare.Compare(x.den.mag, one);
    var numIsZero := |numMag| == 0;
    if numIsZero || denIsOne == 0 {
      // Whole-number case: value is numv/1 or 0/den; printed "[-]D.0".
      // den value is 1 here (Compare == 0 ==> Value(denMag) == Value([1]) == 1).
      var neg := x.num.negative;
      if numIsZero {
        s := "0.0";
        // "0.0" == "" + "0" + "." + "0", neg == false (Wf: no "-0").
        ZeroDigitString();
        WholeValue(x, "0", false);
        assert s == (if false then "-" else "") + "0" + "." + "0";
        assert DenotesSignedDecimal(s, RealValue(x));
        return;
      }
      // den == 1 (denIsOne == 0 and numMag nonempty).
      assert Value(x.den.mag) == Value(one) == 1;
      assert FwInt.IntValue(x.den) == 1;
      var ds := DigitsOf(numMag);          // AllDigits(ds), ParseDec(ds)==Value(numMag)
      s := sign + ds + ".0";
      ZeroDigitString();
      WholeValue(x, ds, neg);
      assert s == (if neg then "-" else "") + ds + "." + "0";
      assert DenotesSignedDecimal(s, RealValue(x));
      return;
    }
    // Fraction-print case: "([-]A.0 / B.0)".
    var neg := x.num.negative;
    var numDigits := DigitsOf(numMag);     // ParseDec == Value(numMag)
    var denDigits := DigitsOf(x.den.mag);  // ParseDec == Value(denMag)
    s := "(" + sign + numDigits + ".0 / " + denDigits + ".0)";
    assert s == FracShape(neg, numDigits, denDigits);
    FractionValue(x, Value(numMag), Value(x.den.mag), neg);
    WitnessFractionPrint(s, RealValue(x), neg, numDigits, denDigits);
    assert DenotesFractionPrint(s, RealValue(x));
  }

  // Introduce the DenotesFractionPrint existential from an explicit witness.
  lemma WitnessFractionPrint(s: seq<char>, v: real, neg: bool, a: seq<char>, b: seq<char>)
    requires FwRealPrint.AllDigits(a) && FwRealPrint.AllDigits(b)
    requires (FwRealPrint.ParseDec(b) as real) != 0.0
    requires s == FracShape(neg, a, b)
    requires v == (if neg then -(FwRealPrint.ParseDec(a) as real) else (FwRealPrint.ParseDec(a) as real))
                  / (FwRealPrint.ParseDec(b) as real)
    ensures DenotesFractionPrint(s, v)
  {
    assert s == FracShape(neg, a, b);   // supplies the trigger term
  }
}

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
 * string, read back as a decimal, equals the real value. ALL THREE shapes it
 * emits are covered, in the same order as C# BigRational.ToString:
 *   1. whole number     "[-]D.0"        (DenotesSignedDecimal, f == "0")
 *   2. terminating dec.  "[-]W.F"       (DenotesSignedDecimal, |F| == log10 >= 1)
 *   3. exact fraction    "([-]A.0 / B.0)" (DenotesFractionPrint)
 * Case 2 is the terminating-decimal / point-placement case ported from
 * src/DafnyReal.dfy: its decision test DividesAPowerOf10Fw runs on the limb
 * representation (DivMod by [10]/[5]/[2], no `Value(den) as nat`), the scale
 * factor is carried as an executable seq<limb> so |num|*factor is computable, and
 * the decimal-place count log10 lives at runtime as the LENGTH of a '0'-string
 * (padZeros), so no compiled nat counter is needed. So e.g. 3/2 prints "1.5" and
 * 1/10 prints "0.1". No int/nat in compiled code, no false ensures (parse-back
 * spec is ghost).
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
include "FwMul.dfy"
include "FwReal.dfy"
include "FwRealPrint.dfy"

module FwRealToString {
  import opened FwNat
  import FwInt
  import opened FwCompare
  import FwDivMod
  import FwMul
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

  //////////////////////////////////////////////////////////////////////////////
  // Pure char / decimal-string helpers for the terminating-decimal case (GHOST).
  // Ported from src/PureArith.dfy (ParseDecConcat, DecimalCutCorrect,
  // DecimalZeroPadCorrect, ...). All pure over seq<char>/nat/real — they never
  // mention the recursive bignum Value, so no heavy axioms enter the proof.
  //////////////////////////////////////////////////////////////////////////////

  lemma AllDigitsConcat(a: seq<char>, b: seq<char>)
    requires FwRealPrint.AllDigits(a) && FwRealPrint.AllDigits(b)
    ensures FwRealPrint.AllDigits(a + b)
  {
    forall i | 0 <= i < |a + b| ensures FwRealPrint.IsDigitChar((a + b)[i]) {
      if i < |a| { assert (a + b)[i] == a[i]; } else { assert (a + b)[i] == b[i - |a|]; }
    }
  }

  lemma MulDistribRightNat(x: nat, y: nat, k: nat)
    ensures (x + y) * k == x * k + y * k
  {}

  lemma MulReassocNat3(a: nat, b: nat, c: nat)
    ensures (a * b) * c == a * (b * c)
  {}

  // The nonlinear closing step of ParseDecConcat, over plain nats.
  lemma ParseDecConcatStep(pa: nat, pb': nat, P: nat, d: nat, m: nat)
    requires P == Pow10(m)
    ensures (pa * P + pb') * 10 + d == pa * Pow10(m + 1) + (pb' * 10 + d)
  {
    calc {
      (pa * P + pb') * 10 + d;
      { MulDistribRightNat(pa * P, pb', 10); }
      (pa * P) * 10 + pb' * 10 + d;
      { MulReassocNat3(pa, P, 10); }
      pa * (P * 10) + (pb' * 10 + d);
      { assert P * 10 == 10 * P; assert Pow10(m + 1) == 10 * Pow10(m); }
      pa * Pow10(m + 1) + (pb' * 10 + d);
    }
  }

  // Concatenation splits ParseDec: value(a ++ b) == value(a)*10^|b| + value(b).
  @IsolateAssertions
  lemma ParseDecConcat(a: seq<char>, b: seq<char>)
    requires FwRealPrint.AllDigits(a) && FwRealPrint.AllDigits(b)
    ensures FwRealPrint.AllDigits(a + b)
    ensures FwRealPrint.ParseDec(a + b)
            == FwRealPrint.ParseDec(a) * Pow10(|b|) + FwRealPrint.ParseDec(b)
    decreases |b|
  {
    AllDigitsConcat(a, b);
    if |b| == 0 {
      assert a + b == a;
    } else {
      var b' := b[..|b| - 1];
      var last := b[|b| - 1];
      assert FwRealPrint.AllDigits(b') by {
        forall i | 0 <= i < |b'| ensures FwRealPrint.IsDigitChar(b'[i]) { assert b'[i] == b[i]; }
      }
      ParseDecConcat(a, b');                    // IH on the shorter b'
      assert (a + b)[..|a + b| - 1] == a + b';
      assert (a + b)[|a + b| - 1] == last;
      assert FwRealPrint.ParseDec(a + b)
             == FwRealPrint.ParseDec(a + b') * 10 + FwRealPrint.DigitVal(last);
      assert FwRealPrint.ParseDec(b)
             == FwRealPrint.ParseDec(b') * 10 + FwRealPrint.DigitVal(last) by {
        assert b[..|b| - 1] == b';
      }
      ParseDecConcatStep(FwRealPrint.ParseDec(a), FwRealPrint.ParseDec(b'),
                         Pow10(|b'|), FwRealPrint.DigitVal(last), |b'|);
    }
  }

  // A string of '0' characters denotes 0.
  lemma ZerosParseToZero(zeros: seq<char>)
    requires FwRealPrint.AllDigits(zeros)
    requires forall i :: 0 <= i < |zeros| ==> zeros[i] == '0'
    ensures FwRealPrint.ParseDec(zeros) == 0
    decreases |zeros|
  {
    if |zeros| == 0 {
    } else {
      var z' := zeros[..|zeros| - 1];
      assert FwRealPrint.AllDigits(z') by {
        forall i | 0 <= i < |z'| ensures FwRealPrint.IsDigitChar(z'[i]) { assert z'[i] == zeros[i]; }
      }
      assert forall i :: 0 <= i < |z'| ==> z'[i] == '0';
      ZerosParseToZero(z');
      assert FwRealPrint.DigitVal(zeros[|zeros| - 1]) == 0;
    }
  }

  // Leading zeros do not change the parsed value.
  lemma ParseDecLeadingZeros(zeros: seq<char>, s: seq<char>)
    requires FwRealPrint.AllDigits(zeros) && FwRealPrint.AllDigits(s)
    requires forall i :: 0 <= i < |zeros| ==> zeros[i] == '0'
    ensures FwRealPrint.AllDigits(zeros + s)
    ensures FwRealPrint.ParseDec(zeros + s) == FwRealPrint.ParseDec(s)
  {
    ParseDecConcat(zeros, s);
    ZerosParseToZero(zeros);
    assert FwRealPrint.ParseDec(zeros + s)
           == FwRealPrint.ParseDec(zeros) * Pow10(|s|) + FwRealPrint.ParseDec(s);
  }

  // Real step: m == wv*P + fv (P>=1) ==> wv + fv/P == m/P.
  lemma DecimalCutReal(wv: nat, fv: nat, m: nat, P: nat)
    requires P >= 1
    requires m == wv * P + fv
    ensures (wv as real) + (fv as real) / (P as real) == (m as real) / (P as real)
  {
    var Pr := P as real;
    assert Pr > 0.0;
    assert (wv * P) as real == (wv as real) * Pr;
    assert (m as real) == (wv as real) * Pr + (fv as real);
    assert (m as real) / Pr == (wv as real) * Pr / Pr + (fv as real) / Pr;
    assert (wv as real) * Pr / Pr == (wv as real);
  }

  // Decimal-point placement identity: digits of m, cut log10 from the right,
  // layout value equals m / 10^log10.
  @IsolateAssertions
  lemma DecimalCutCorrect(digits: seq<char>, cut: nat, log10: nat, m: nat)
    requires FwRealPrint.AllDigits(digits)
    requires FwRealPrint.ParseDec(digits) == m
    requires cut + log10 == |digits|
    requires cut <= |digits|
    ensures FwRealPrint.AllDigits(digits[..cut]) && FwRealPrint.AllDigits(digits[cut..])
    ensures |digits[cut..]| == log10
    ensures (FwRealPrint.ParseDec(digits[..cut]) as real)
            + (FwRealPrint.ParseDec(digits[cut..]) as real) / (Pow10(log10) as real)
            == (m as real) / (Pow10(log10) as real)
  {
    var w := digits[..cut];
    var f := digits[cut..];
    assert FwRealPrint.AllDigits(w) by {
      forall i | 0 <= i < |w| ensures FwRealPrint.IsDigitChar(w[i]) { assert w[i] == digits[i]; }
    }
    assert FwRealPrint.AllDigits(f) by {
      forall i | 0 <= i < |f| ensures FwRealPrint.IsDigitChar(f[i]) { assert f[i] == digits[cut + i]; }
    }
    assert w + f == digits;
    ParseDecConcat(w, f);
    assert |f| == log10;
    var P := Pow10(log10);
    DecimalCutReal(FwRealPrint.ParseDec(w), FwRealPrint.ParseDec(f), m, P);
  }

  // Zero-integer-part layout: "0." + zeros + digits denotes m / 10^log10.
  lemma DecimalZeroPadCorrect(zeros: seq<char>, digits: seq<char>, log10: nat, m: nat)
    requires FwRealPrint.AllDigits(zeros) && FwRealPrint.AllDigits(digits)
    requires forall i :: 0 <= i < |zeros| ==> zeros[i] == '0'
    requires FwRealPrint.ParseDec(digits) == m
    requires |zeros| + |digits| == log10
    ensures FwRealPrint.AllDigits(zeros + digits)
    ensures |zeros + digits| == log10
    ensures (0 as real) + (FwRealPrint.ParseDec(zeros + digits) as real) / (Pow10(log10) as real)
            == (m as real) / (Pow10(log10) as real)
  {
    ParseDecLeadingZeros(zeros, digits);
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

  //////////////////////////////////////////////////////////////////////////////
  // Fixed-width "does the denominator divide a power of ten?" test, the terminating
  // -decimal decision of C# BigRational.DividesAPowerOf10 / src/PureArith's
  // DividesAPowerOf10 — but on the limb representation, with NO `Value(den) as nat`
  // in compiled code. The divisibility tests are DivMod by [10]/[5]/[2] with an
  // |r|==0 check; the scaling factor is carried as an executable seq<limb>
  // (factorSeq) built by FwMul.Mul, so num*factor is later computable. log10 is a
  // ghost witness only. ensures: ok ==> Value(factorSeq)*Value(den) == Pow10(log10).
  //////////////////////////////////////////////////////////////////////////////

  // padZeros is the executable "log10 '0's" string: its LENGTH carries log10 at
  // runtime (seq length, not a nat counter), so the zero-pad / point-placement
  // arithmetic in ToString needs no compiled nat. ghost log10 mirrors |padZeros|.
  method DividesAPowerOf10Fw(den: seq<limb>)
      returns (ok: bool, factorSeq: seq<limb>, padZeros: seq<char>, ghost log10: nat)
    requires Normalized(den)
    requires Value(den) > 0
    ensures Normalized(factorSeq)
    ensures |padZeros| == log10
    ensures forall i :: 0 <= i < |padZeros| ==> padZeros[i] == '0'
    ensures ok ==> Value(factorSeq) * Value(den) == Pow10(log10)
    decreases Value(den)
  {
    TenValue();
    var one: seq<limb> := [1 as limb];
    assert Value(one) == 1;
    var cmpOne := FwCompare.Compare(den, one);
    if cmpOne == 0 {
      // Value(den) == 1: factor 1, log10 0, 1*1 == Pow10(0).
      ok := true; factorSeq := one; padZeros := ""; log10 := 0;
      assert Value(factorSeq) * Value(den) == 1 == Pow10(0);
      return;
    }
    // Value(den) >= 2 here (den != 0 and den != 1).
    DenAtLeastTwo(den, one, cmpOne);
    var ten: seq<limb> := [10 as limb];
    var five: seq<limb> := [5 as limb];
    var two: seq<limb> := [2 as limb];
    assert Value(ten) == 10 && Value(five) == 5 && Value(two) == 2;

    var q10, r10 := FwDivMod.DivMod(den, ten);
    if |r10| == 0 {
      // den % 10 == 0, recurse on q10 == den/10, factor multiplier 1.
      DivExactQuotient(den, ten, q10, r10, 10);
      var okr, fr, pz, l10r := DividesAPowerOf10Fw(q10);
      padZeros := "0" + pz;
      log10 := l10r + 1;
      if okr {
        factorSeq := fr;
        StepPow10(Value(fr), Value(fr), Value(den), Value(q10), 10, 1, l10r);
        ok := true;
        return;
      }
      ok := false; factorSeq := one;
      return;
    }
    var q5, r5 := FwDivMod.DivMod(den, five);
    if |r5| == 0 {
      DivExactQuotient(den, five, q5, r5, 5);
      var okr, fr, pz, l10r := DividesAPowerOf10Fw(q5);
      padZeros := "0" + pz;
      log10 := l10r + 1;
      if okr {
        factorSeq := FwMul.Mul(two, fr);       // 2 * fr
        StepPow10(Value(factorSeq), Value(fr), Value(den), Value(q5), 5, 2, l10r);
        ok := true;
        return;
      }
      ok := false; factorSeq := one;
      return;
    }
    var q2, r2 := FwDivMod.DivMod(den, two);
    if |r2| == 0 {
      DivExactQuotient(den, two, q2, r2, 2);
      var okr, fr, pz, l10r := DividesAPowerOf10Fw(q2);
      padZeros := "0" + pz;
      log10 := l10r + 1;
      if okr {
        factorSeq := FwMul.Mul(five, fr);      // 5 * fr
        StepPow10(Value(factorSeq), Value(fr), Value(den), Value(q2), 2, 5, l10r);
        ok := true;
        return;
      }
      ok := false; factorSeq := one;
      return;
    }
    // den not divisible by 2 or 5, and den != 1: cannot divide a power of ten.
    ok := false; factorSeq := one; padZeros := ""; log10 := 0;
  }

  // Compare(den,[1]) != 0 with Value(den) > 0 forces Value(den) >= 2.
  lemma DenAtLeastTwo(den: seq<limb>, one: seq<limb>, cmpOne: cmp)
    requires Value(one) == 1 && Value(den) > 0
    requires (cmpOne == 0) <==> (Value(den) == Value(one))
    requires cmpOne != 0
    ensures Value(den) >= 2
  {}

  // DivMod(den, d) with empty remainder: Value(den) == Value(q)*d exactly, and
  // the quotient strictly decreases (d >= 2, Value(den) >= 2).
  lemma DivExactQuotient(den: seq<limb>, dseq: seq<limb>, q: seq<limb>, r: seq<limb>,
                         d: nat)
    requires d >= 2
    requires Value(dseq) == d
    requires Value(den) >= 2
    requires Normalized(q) && Normalized(r)
    requires Value(den) == Value(q) * Value(dseq) + Value(r)
    requires Value(r) < Value(dseq)
    requires |r| == 0
    ensures Value(den) == Value(q) * d
    ensures Value(q) > 0
    ensures Value(q) < Value(den)
  {
    assert Value(r) == 0;
    // Pull the magnitudes out to plain nats; the inequality is pure nat algebra
    // (no recursive Value in scope for SMT to expand on).
    ghost var qv := Value(q);
    ghost var dv := Value(den);
    assert dv == qv * d;
    DivExactNat(qv, dv, d);
  }

  // Pure nat core of DivExactQuotient: dv == qv*d, d >= 2, dv >= 2 ==> qv in (0, dv).
  lemma DivExactNat(qv: nat, dv: nat, d: nat)
    requires d >= 2 && dv >= 2 && dv == qv * d
    ensures qv > 0
    ensures qv < dv
  {
    if qv == 0 { assert dv == 0; }
    assert qv * d >= qv * 2;
    assert qv * 2 == qv + qv;
  }

  // One recursion step: factorSub*Value(q) == Pow10(l') and Value(den) == Value(q)*d
  // and fNew == mult*factorSub and mult*d == 10 ==> fNew*Value(den) == Pow10(l'+1).
  lemma StepPow10(fNew: nat, factorSub: nat, denv: nat, qv: nat, d: nat, mult: nat, l: nat)
    requires denv == qv * d
    requires factorSub * qv == Pow10(l)
    requires fNew == mult * factorSub
    requires mult * d == 10
    ensures fNew * denv == Pow10(l + 1)
  {
    calc {
      fNew * denv;
      (mult * factorSub) * (qv * d);
      { MulReassoc4(mult, factorSub, qv, d); }
      (mult * d) * (factorSub * qv);
      10 * Pow10(l);
      Pow10(l + 1);
    }
  }

  lemma MulReassoc4(a: nat, b: nat, c: nat, d: nat)
    ensures (a * b) * (c * d) == (a * d) * (b * c)
  {}

  //////////////////////////////////////////////////////////////////////////////
  // Value lemmas for the terminating-decimal case (GHOST), ported from the
  // TerminatingCase of src/DafnyReal.dfy's ToStringCorrect. pa == |num|, pb == den,
  // factor*pb == Pow10(log10), nAbs == pa*factor. RealValue(x) == (neg? -nAbs : nAbs)
  // / Pow10(log10).
  //////////////////////////////////////////////////////////////////////////////

  // RealValue(x) == (neg? -nAbs : nAbs) / Pow10(log10), where pa == |IntValue(num)|
  // == Value(numMag), pb == Value(denMag), nAbs == pa*factor, factor*pb==Pow10(log10).
  @IsolateAssertions
  lemma TerminatingValue(x: Real, pa: nat, pb: nat, factor: nat, log10: nat,
                         nAbs: nat, neg: bool)
    requires Wf(x)
    requires pa == Value(x.num.mag) && pb == Value(x.den.mag)
    requires neg == x.num.negative
    requires factor * pb == Pow10(log10)
    requires nAbs == pa * factor
    requires pb > 0
    ensures RealValue(x)
            == (if neg then -(nAbs as real) else (nAbs as real)) / (Pow10(log10) as real)
  {
    var numv := FwInt.IntValue(x.num);
    var denv := FwInt.IntValue(x.den);
    IntValueAbs(x.num);
    IntValueAbs(x.den);
    assert denv == pb as int;
    // numv == (neg? -pa : pa).
    var P := Pow10(log10);
    var fr := factor as real;
    var dr := pb as real;
    var Pr := P as real;
    assert dr > 0.0;
    // factor*pb == P (over reals), fr*dr == Pr, fr > 0.
    assert (factor * pb) as real == fr * dr;
    assert fr * dr == Pr;
    assert Pr >= 1.0;
    assert fr > 0.0 by { if fr <= 0.0 { assert fr * dr <= 0.0; } }
    // nAbs as real == pa*fr.
    assert (nAbs as real) == (pa as real) * fr;
    // RealValue == numv/denv == (signed pa)/pb.
    assert RealValue(x) == (numv as real) / (dr);
    if neg {
      assert numv == -(pa as int);
      assert (numv as real) == -(pa as real);
    } else {
      assert numv == pa as int;
      assert (numv as real) == pa as real;
    }
    // (pa/pb) == (pa*fr)/(pb*fr) == nAbs/P.
    TermScaleReal(pa as real, dr, fr, nAbs as real, Pr);
    assert (pa as real) / dr == (nAbs as real) / Pr;
    // RealValue == (signed pa)/dr; push the sign through the equal quotients.
    SignedQuotientEq(neg, pa, nAbs, dr, Pr);
    assert RealValue(x)
           == (if neg then -(nAbs as real) else (nAbs as real)) / Pr;
  }

  // If pa/dr == nAbs/Pr then (±pa)/dr == (±nAbs)/Pr (same sign flag).
  lemma SignedQuotientEq(neg: bool, pa: nat, nAbs: nat, dr: real, Pr: real)
    requires dr > 0.0 && Pr > 0.0
    requires (pa as real) / dr == (nAbs as real) / Pr
    ensures (if neg then -(pa as real) else (pa as real)) / dr
            == (if neg then -(nAbs as real) else (nAbs as real)) / Pr
  {
    if neg {
      assert (-(pa as real)) / dr == -((pa as real) / dr);
      assert (-(nAbs as real)) / Pr == -((nAbs as real) / Pr);
    }
  }

  // pa/dr == (pa*fr)/(dr*fr) and dr*fr == Pr ==> pa/dr == nr/Pr.
  lemma TermScaleReal(pa: real, dr: real, fr: real, nr: real, Pr: real)
    requires dr > 0.0 && fr > 0.0
    requires nr == pa * fr
    requires dr * fr == Pr
    ensures pa / dr == nr / Pr
  {
    assert Pr == dr * fr;
    assert pa / dr == (pa * fr) / (dr * fr) by {
      RealCancel(pa, dr, fr);
    }
  }

  // (x/y) == (x*z)/(y*z) for y,z != 0.
  lemma RealCancel(a: real, b: real, c: real)
    requires b != 0.0 && c != 0.0
    ensures a / b == (a * c) / (b * c)
  {}

  // (n as real)/P with m==|n| equals (neg? -(m/P) : m/P).
  lemma SignDivReal(nAbs: nat, P: nat, neg: bool)
    requires P >= 1
    ensures (if neg then -(nAbs as real) else (nAbs as real)) / (P as real)
            == (if neg then -((nAbs as real) / (P as real)) else (nAbs as real) / (P as real))
  {
    assert (P as real) > 0.0;
  }

  // Layout (neg, w, f) with w=digits[..cut], f=digits[cut..] equals signed nAbs/P.
  @IsolateAssertions
  lemma SignedLayoutValue(neg: bool, w: seq<char>, f: seq<char>, nAbs: nat, P: nat, log10: nat)
    requires FwRealPrint.AllDigits(w) && FwRealPrint.AllDigits(f)
    requires P >= 1 && P == Pow10(log10) && |f| == log10
    requires (FwRealPrint.ParseDec(w) as real)
             + (FwRealPrint.ParseDec(f) as real) / (P as real)
             == (nAbs as real) / (P as real)
    ensures (if neg then -(nAbs as real) else (nAbs as real)) / (P as real)
            == DecimalLayoutValue(neg, w, f)
  {
    var mag := (FwRealPrint.ParseDec(w) as real)
             + (FwRealPrint.ParseDec(f) as real) / (Pow10(|f|) as real);
    assert mag == (nAbs as real) / (P as real);
    SignDivReal(nAbs, P, neg);
  }

  // Zero-pad layout: w == "0", f == zeros++digits; value 0 + nAbs/P == signed nAbs/P.
  @IsolateAssertions
  lemma ZeroPadLayoutValue(neg: bool, w: seq<char>, f: seq<char>, nAbs: nat, P: nat, log10: nat)
    requires w == "0" && FwRealPrint.AllDigits(f)
    requires P >= 1 && P == Pow10(log10) && |f| == log10
    requires (0 as real) + (FwRealPrint.ParseDec(f) as real) / (P as real)
             == (nAbs as real) / (P as real)
    ensures (if neg then -(nAbs as real) else (nAbs as real)) / (P as real)
            == DecimalLayoutValue(neg, w, f)
  {
    assert FwRealPrint.AllDigits(w) by { assert w[0] == '0'; }
    assert FwRealPrint.ParseDec(w) == 0 by {
      assert w[..|w| - 1] == [];
      assert FwRealPrint.DigitVal(w[0]) == 0;
    }
    var mag := (FwRealPrint.ParseDec(w) as real)
             + (FwRealPrint.ParseDec(f) as real) / (Pow10(|f|) as real);
    assert mag == (nAbs as real) / (P as real);
    SignDivReal(nAbs, P, neg);
  }

  // den != 1 and factor*den == Pow10(log10) ==> log10 >= 1.
  lemma Log10Pos(denv: nat, factor: nat, log10: nat)
    requires denv >= 2
    requires factor * denv == Pow10(log10)
    ensures log10 >= 1
  {
    if log10 == 0 {
      assert Pow10(0) == 1;
      assert factor * denv == 1;
      assert denv >= 2;
    }
  }

  // Split a digit string into (w, f) with f the suffix of the SAME length as
  // marker, w the prefix. Peels characters off the front by LENGTH-EQUALITY only
  // (no |digits|-|marker| int arithmetic), so the C++ backend stays Boost-free.
  method SplitSuffix(digits: seq<char>, marker: seq<char>) returns (w: seq<char>, f: seq<char>)
    requires |marker| <= |digits|
    ensures w + f == digits
    ensures |f| == |marker|
    ensures w == digits[..|digits| - |marker|]
    ensures f == digits[|digits| - |marker|..]
    decreases |digits|
  {
    if |digits| == |marker| {
      w := "";
      f := digits;
      assert w + f == digits;
      return;
    }
    // |digits| > |marker| >= 0, so digits is nonempty; peel its head.
    var head := digits[..1];
    var w', f' := SplitSuffix(digits[1..], marker);
    w := head + w';
    f := f';
    SplitSuffixFold(digits, marker, head, w', f', w);
  }

  // Gluing lemma for SplitSuffix: head ++ (prefix of the tail) is the prefix of
  // the whole, and the suffix is unchanged.
  lemma SplitSuffixFold(digits: seq<char>, marker: seq<char>, head: seq<char>,
                        w': seq<char>, f': seq<char>, w: seq<char>)
    requires |marker| < |digits|
    requires head == digits[..1]
    requires w' + f' == digits[1..]
    requires |f'| == |marker|
    requires w' == digits[1..][..|digits[1..]| - |marker|]
    requires f' == digits[1..][|digits[1..]| - |marker|..]
    requires w == head + w'
    ensures w + f' == digits
    ensures w == digits[..|digits| - |marker|]
    ensures f' == digits[|digits| - |marker|..]
  {
    assert head + digits[1..] == digits;
    assert w + f' == head + (w' + f') == head + digits[1..] == digits;
    assert w == digits[..|digits| - |marker|];
    assert f' == digits[|digits| - |marker|..];
  }

  // num != 0 and den != 1 (Compare(denMag,[1]) != 0) with Wf ==> Value(denMag) >= 2.
  lemma DenMagAtLeastTwo(x: Real, one: seq<limb>, denIsOne: cmp)
    requires Wf(x)
    requires Value(one) == 1
    requires (denIsOne == 0) <==> (Value(x.den.mag) == Value(one))
    requires denIsOne != 0
    ensures Value(x.den.mag) >= 2
  {
    // den > 0 (Wf) and den != 1, so den >= 2.
    assert FwInt.IntValue(x.den) > 0;
    IntValueAbs(x.den);
    assert Value(x.den.mag) > 0;
  }

  // zeros == padZeros[|digits|..] with |padZeros| == log10 >= |digits|: zeros is
  // all '0', AllDigits, and |zeros| + |digits| == log10.
  lemma ZerosSliceFacts(padZeros: seq<char>, digits: seq<char>, zeros: seq<char>, log10: nat)
    requires |padZeros| == log10 && |padZeros| >= |digits|
    requires forall i :: 0 <= i < |padZeros| ==> padZeros[i] == '0'
    requires zeros == padZeros[|digits|..]
    ensures forall i :: 0 <= i < |zeros| ==> zeros[i] == '0'
    ensures FwRealPrint.AllDigits(zeros)
    ensures |zeros| + |digits| == log10
  {
    forall i | 0 <= i < |zeros| ensures zeros[i] == '0' { assert zeros[i] == padZeros[|digits| + i]; }
    assert FwRealPrint.AllDigits(zeros) by {
      forall i | 0 <= i < |zeros| ensures FwRealPrint.IsDigitChar(zeros[i]) { assert zeros[i] == '0'; }
    }
  }

  // Introduce the DenotesSignedDecimal existential from an explicit witness.
  lemma WitnessSignedDecimal(s: seq<char>, v: real, neg: bool, w: seq<char>, f: seq<char>)
    requires FwRealPrint.AllDigits(w) && FwRealPrint.AllDigits(f) && |f| >= 1
    requires s == (if neg then "-" else "") + w + "." + f
    requires v == DecimalLayoutValue(neg, w, f)
    ensures DenotesSignedDecimal(s, v)
  {}

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
    // From here num != 0 and den != 1, so Value(denMag) >= 2.
    var neg := x.num.negative;
    DenMagAtLeastTwo(x, one, denIsOne);

    // Terminating-decimal case: den divides a power of ten. Mirrors C#'s
    // DividesAPowerOf10 branch (BigRational.ToString) / src TerminatingCase. The
    // digit count log10 lives at runtime as |padZeros| (padZeros is log10 '0's).
    var ok, factorSeq, padZeros, log10 := DividesAPowerOf10Fw(x.den.mag);
    assert |padZeros| == log10;
    if ok {
      // num/den == (num*factor)/10^log10. Compute |num|*factor as a limb seq and
      // place the point |padZeros| places from the right.
      assert Value(factorSeq) * Value(x.den.mag) == Pow10(log10);
      Log10Pos(Value(x.den.mag), Value(factorSeq), log10);
      assert log10 >= 1 && |padZeros| >= 1;
      var scaledMag := FwMul.Mul(numMag, factorSeq);   // Value == Value(numMag)*factor
      assert Value(scaledMag) == Value(numMag) * Value(factorSeq);
      ghost var nAbs := Value(scaledMag);
      TerminatingValue(x, Value(numMag), Value(x.den.mag), Value(factorSeq),
                       log10, nAbs, neg);
      assert RealValue(x)
             == (if neg then -(nAbs as real) else (nAbs as real)) / (Pow10(log10) as real);
      var digits := DigitsOf(scaledMag);  // AllDigits, ParseDec(digits)==Value(scaledMag)==nAbs
      assert FwRealPrint.ParseDec(digits) == nAbs;
      ghost var P := Pow10(log10);
      if |padZeros| < |digits| {
        // cut log10 (== |padZeros|) from the right: w.f with |f| == log10. The
        // split point |digits|-log10 is NOT computed as an int (that would need a
        // non-native subtraction); SplitSuffix peels characters by length-equality.
        var w, f := SplitSuffix(digits, padZeros);
        assert |f| == |padZeros| == log10;
        assert w + f == digits && w == digits[..|digits| - |padZeros|];
        DecimalCutCorrect(digits, |digits| - |padZeros|, log10, nAbs);
        assert |f| == log10;
        s := sign + w + "." + f;
        assert s == (if neg then "-" else "") + w + "." + f;
        SignedLayoutValue(neg, w, f, nAbs, P, log10);
        assert RealValue(x) == DecimalLayoutValue(neg, w, f);
        WitnessSignedDecimal(s, RealValue(x), neg, w, f);
        assert DenotesReal(s, RealValue(x));
        return;
      } else {
        // more fractional places than digits: "0." + zeros + digits, where the
        // leading-zero count is |padZeros| - |digits| (a runtime slice of padZeros).
        var zeros := padZeros[|digits|..];
        var w := "0";
        var f := zeros + digits;
        ZerosSliceFacts(padZeros, digits, zeros, log10);
        DecimalZeroPadCorrect(zeros, digits, log10, nAbs);
        assert FwRealPrint.AllDigits(f) && |f| == log10;
        s := sign + w + "." + f;
        assert s == (if neg then "-" else "") + w + "." + f;
        ZeroPadLayoutValue(neg, w, f, nAbs, P, log10);
        assert RealValue(x) == DecimalLayoutValue(neg, w, f);
        WitnessSignedDecimal(s, RealValue(x), neg, w, f);
        assert DenotesReal(s, RealValue(x));
        return;
      }
    }

    // Fraction-print case: "([-]A.0 / B.0)".
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

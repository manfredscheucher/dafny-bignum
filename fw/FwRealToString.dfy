/*******************************************************************************
 * dafny-bignum / fixed-width: FwRealToString
 *
 * Decimal rendering of FwReal, modelling Dafny BigRational.ToString.
 *
 * VERIFIED (Gate 1): the digit machinery is fixed-width and proven — `DigitsOf`
 * extracts the decimal digits of a limb magnitude by repeated FwDivMod.DivMod by
 * [10] (NOT nat division), the digit char is a constant-string index by the
 * remainder limb, lengths are sequence lengths, and the result is proven to
 * denote Value(mag) via ParseDec. No int/nat in compiled code, no false ensures.
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
      FwDivMod.Pow32Positive(|r| - 1);
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
    FwDivMod.Pow32Positive(k - 1);
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

  // ToString: the whole-number case prints "sign D.0"; otherwise the exact
  // value as Dafny's "(num.0 / den.0)" form. Digits via the verified DigitsOf.
  // (Not the terminating-decimal point placement — that is proven in src/; here
  // the exact fraction form is always a faithful rendering.)
  method ToString(x: Real) returns (s: seq<char>)
    requires Wf(x)
  {
    var numMag := x.num.mag;
    var sign: seq<char> := if x.num.negative then "-" else "";
    var one: seq<limb> := [1 as limb];
    TenValue();
    var denIsOne := FwCompare.Compare(x.den.mag, one);
    var numIsZero := |numMag| == 0;
    if numIsZero || denIsOne == 0 {
      if numIsZero {
        return "0.0";
      }
      var ds := DigitsOf(numMag);
      return sign + ds + ".0";
    }
    var numDigits := DigitsOf(numMag);
    var denDigits := DigitsOf(x.den.mag);
    s := "(" + sign + numDigits + ".0 / " + denDigits + ".0)";
  }
}

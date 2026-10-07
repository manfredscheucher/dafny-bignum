/*******************************************************************************
 * dafny-bignum / fixed-width: FwInt
 *
 * Signed sign+magnitude integer on top of the fixed-width BigNat stack
 * (FwNat/FwSub/FwMul/FwCompare/FwDivMod.Normalize). Same hard rule: every
 * executable value is a fixed-width newtype (limb/dword/cmp) or bool/seq;
 * int/nat appear only in ghost specs and lemmas, so the generated code stays
 * Boost-free (native uint32/uint64/bool).
 *
 *   Int(negative, mag)   mag a normalized little-endian limb sequence,
 *   Wf: mag normalized and (mag==[] ==> !negative), so there is no "-0".
 *   IntValue(x) = (-1)^negative * Value(mag).
 *
 * Add/Sub/Compare/Mul reduce to the unsigned operations by sign case.
 *******************************************************************************/

include "FwNat.dfy"
include "FwSub.dfy"
include "FwMul.dfy"
include "FwCompare.dfy"
include "FwDivMod.dfy"

module FwInt {
  import opened FwNat
  import FwSub
  import FwMul
  import opened FwCompare
  import FwDivMod

  // sign + magnitude.  bool is a native type, so it is fine in compiled code.
  datatype Int = Int(negative: bool, mag: seq<limb>)

  ghost predicate Wf(x: Int)
  {
    Normalized(x.mag) && (x.mag == [] ==> !x.negative)
  }

  // The mathematical integer denoted.
  ghost function IntValue(x: Int): int
  {
    if x.negative then -(Value(x.mag) as int) else Value(x.mag) as int
  }

  //////////////////////////////////////////////////////////////////////////////
  // A normalized nonempty magnitude is strictly positive.
  //////////////////////////////////////////////////////////////////////////////

  lemma NonEmptyMagPositive(mag: seq<limb>)
    requires Normalized(mag) && mag != []
    ensures Value(mag) > 0
  {
    FwCompare.TopLimbLowerBound(mag);      // Value(mag) >= Pow32(|mag|-1)
    Pow32Positive(|mag| - 1);     // Pow32(|mag|-1) >= 1
  }

  //////////////////////////////////////////////////////////////////////////////
  // Length-aligning unsigned helpers (AddSeq/SubSeq need equal lengths).
  //////////////////////////////////////////////////////////////////////////////

  // Unsigned add of any-length sequences; exact Value. Reuses FwMul.AddFull.
  method UAdd(xs: seq<limb>, ys: seq<limb>) returns (zs: seq<limb>)
    ensures Value(zs) == Value(xs) + Value(ys)
  {
    zs := FwMul.AddFull(xs, ys);
  }

  // Unsigned subtract, requires Value(ys) <= Value(xs). Pads to equal length,
  // subtracts, and the final borrow is 0 (since ys <= xs). Value exact.
  method USub(xs: seq<limb>, ys: seq<limb>) returns (zs: seq<limb>)
    requires Value(ys) <= Value(xs)
    ensures Value(zs) == Value(xs) - Value(ys)
  {
    var xp, yp := FwMul.PadEqual(xs, ys);
    var d, bout := FwSub.SubSeq(xp, yp, 0);
    // bout must be 0: Value(xp) + bout*Pow32 == Value(yp) + Value(d), and
    // Value(yp)=Value(ys) <= Value(xs)=Value(xp), so Value(d) = Value(xp)-Value(yp)
    // >= 0 forces bout == 0 (else Value(d) would need to absorb a full Pow32).
    USubBorrowZero(xp, yp, d, bout);
    zs := d;
  }

  // From the borrow identity with Value(yp) <= Value(xp), the out-borrow is 0.
  lemma USubBorrowZero(xp: seq<limb>, yp: seq<limb>, d: seq<limb>, bout: limb)
    requires |xp| == |yp| == |d|
    requires bout == 0 || bout == 1
    requires Value(xp) + (bout as nat) * Pow32(|xp|) == Value(yp) + Value(d)
    requires Value(yp) <= Value(xp)
    ensures bout == 0
    ensures Value(d) == Value(xp) - Value(yp)
  {
    if bout == 1 {
      // Value(d) = Value(xp) - Value(yp) + Pow32(|xp|) >= Pow32(|xp|),
      // but Value(d) < Pow32(|d|) == Pow32(|xp|). Contradiction.
      FwCompare.ValueBound(d);
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Constructors.
  //////////////////////////////////////////////////////////////////////////////

  // Normalize the magnitude and clear the sign when the value is zero.
  method Make(neg: bool, mag: seq<limb>) returns (r: Int)
    ensures Wf(r)
    ensures IntValue(r) == (if neg then -(Value(mag) as int) else Value(mag) as int)
  {
    var m := FwDivMod.Normalize(mag);      // Normalized(m), Value(m)==Value(mag)
    if |m| == 0 {
      r := Int(false, []);
      assert Value(m) == 0;
    } else {
      r := Int(neg, m);
    }
  }

  method FromMagnitude(mag: seq<limb>) returns (r: Int)
    ensures Wf(r) && IntValue(r) == Value(mag)
  {
    r := Make(false, mag);
  }

  // Negation, canonicalising zero.
  method Negate(x: Int) returns (r: Int)
    requires Wf(x)
    ensures Wf(r)
    ensures IntValue(r) == -IntValue(x)
  {
    if |x.mag| == 0 {
      r := x;
    } else {
      r := Int(!x.negative, x.mag);
    }
  }

  // Absolute value.
  method Abs(x: Int) returns (r: Int)
    requires Wf(x)
    ensures Wf(r)
    ensures IntValue(r) >= 0
    ensures IntValue(r) == (if IntValue(x) < 0 then -IntValue(x) else IntValue(x))
  {
    r := Int(false, x.mag);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Comparison: returns cmp in {-1,0,1}.
  //////////////////////////////////////////////////////////////////////////////

  method Compare(x: Int, y: Int) returns (c: cmp)
    requires Wf(x) && Wf(y)
    ensures c == 0 <==> IntValue(x) == IntValue(y)
    ensures c < 0 <==> IntValue(x) < IntValue(y)
    ensures c > 0 <==> IntValue(x) > IntValue(y)
  {
    if !x.negative && !y.negative {
      c := FwCompare.Compare(x.mag, y.mag);
    } else if x.negative && y.negative {
      // both negative: order reverses on magnitudes. Negate the cmp by a native
      // case split (no int cast, which would compile to an unbounded integer).
      var cm := FwCompare.Compare(x.mag, y.mag);
      if cm < 0 { c := 1; } else if cm > 0 { c := -1; } else { c := 0; }
    } else if x.negative && !y.negative {
      // x < 0 <= y: x.mag nonempty (Wf+negative), so IntValue(x) < 0 <= IntValue(y)
      NonEmptyMagPositive(x.mag);
      c := -1;
    } else {
      // x >= 0 > y
      NonEmptyMagPositive(y.mag);
      c := 1;
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Addition, by sign case.
  //////////////////////////////////////////////////////////////////////////////

  method Add(x: Int, y: Int) returns (r: Int)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures IntValue(r) == IntValue(x) + IntValue(y)
  {
    if x.negative == y.negative {
      // same sign: add magnitudes, keep sign
      var m := UAdd(x.mag, y.mag);
      r := Make(x.negative, m);
    } else {
      // opposite signs: larger magnitude minus smaller; sign follows the larger
      var cm := FwCompare.Compare(x.mag, y.mag);
      if cm == 0 {
        r := Int(false, []);
        AddOppositeEqual(x, y);
      } else if cm > 0 {
        // |x| > |y|: magnitude |x|-|y|, x's sign
        var m := USub(x.mag, y.mag);
        r := Make(x.negative, m);
      } else {
        // |y| > |x|: magnitude |y|-|x|, y's sign
        var m := USub(y.mag, x.mag);
        r := Make(y.negative, m);
      }
    }
  }

  // Opposite signs with equal magnitude ==> sum is zero.
  lemma AddOppositeEqual(x: Int, y: Int)
    requires Wf(x) && Wf(y)
    requires x.negative != y.negative
    requires Value(x.mag) == Value(y.mag)
    ensures IntValue(x) + IntValue(y) == 0
  {}

  method Sub(x: Int, y: Int) returns (r: Int)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures IntValue(r) == IntValue(x) - IntValue(y)
  {
    var ny := Negate(y);
    r := Add(x, ny);
  }

  //////////////////////////////////////////////////////////////////////////////
  // Multiplication: magnitudes multiply, signs xor, zero canonical.
  //////////////////////////////////////////////////////////////////////////////

  method Mul(x: Int, y: Int) returns (r: Int)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures IntValue(r) == IntValue(x) * IntValue(y)
  {
    var m := FwMul.Mul(x.mag, y.mag);      // Value(m) == Value(x.mag)*Value(y.mag)
    MulSignValue(x, y, m);
    r := Make(x.negative != y.negative, m);
  }

  // Value(m) == Value(x.mag)*Value(y.mag) relates to IntValue(x)*IntValue(y).
  lemma MulSignValue(x: Int, y: Int, m: seq<limb>)
    requires Value(m) == Value(x.mag) * Value(y.mag)
    ensures (if (x.negative != y.negative) then -(Value(m) as int) else Value(m) as int)
            == IntValue(x) * IntValue(y)
  {
    // four sign cases; each pulls the sign out of a product of magnitudes.
  }
}

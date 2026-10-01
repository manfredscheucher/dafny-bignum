/*******************************************************************************
 * dafny-bignum: BigInt
 *
 * Signed arbitrary-precision integers: a sign flag plus an unsigned magnitude
 * (a normalized BigNat). Specified against IntValue(), the mathematical integer
 * denoted. Zero is canonical: magnitude [] with negative == false, so there is
 * no "-0".
 *
 * Addition, subtraction, multiplication, comparison, negation and abs are
 * reduced to the verified BigNat operations. GCD is sign-independent and lives
 * on the unsigned layer (BigNatGCD); signed division is not provided here.
 *******************************************************************************/

include "BigNat.dfy"
include "BigNatAddSub.dfy"
include "BigNatMul.dfy"

module BigInt {
  import opened BigNat
  import BigNatAddSub
  import BigNatMul

  // sign + magnitude. The invariant Wf keeps the representation canonical.
  datatype Int = Int(negative: bool, mag: seq<limb>)

  predicate Wf(x: Int)
  {
    Normalized(x.mag) && (x.mag == [] ==> !x.negative)
  }

  // The mathematical integer denoted.
  function IntValue(x: Int): int
  {
    if x.negative then -(Value(x.mag) as int) else Value(x.mag) as int
  }

  // A well-formed number with a nonempty magnitude has strictly positive
  // magnitude (normalized nonempty => not all-zero => Value > 0).
  lemma NonEmptyMagPositive(x: Int)
    requires Wf(x) && x.mag != []
    ensures Value(x.mag) > 0
  {
    if Value(x.mag) == 0 {
      NormalizedZeroUnique(x.mag);   // would force x.mag == [], contradiction
    }
  }

  // Smart constructor: normalize magnitude and clear the sign on zero.
  function Make(neg: bool, mag: seq<limb>): (r: Int)
    ensures Wf(r)
    ensures IntValue(r) == (if neg then -(Value(mag) as int) else Value(mag) as int)
  {
    var m := Normalize(mag);
    if m == [] then Int(false, []) else Int(neg, m)
  }

  const Zero: Int := Int(false, [])

  lemma ZeroValue() ensures IntValue(Zero) == 0 {}

  function FromMagnitude(mag: seq<limb>): (r: Int)
    ensures Wf(r) && IntValue(r) == Value(mag)
  {
    Make(false, mag)
  }

  // Negation: flip the sign, canonicalising zero.
  function Negate(x: Int): (r: Int)
    requires Wf(x)
    ensures Wf(r)
    ensures IntValue(r) == -IntValue(x)
  {
    if x.mag == [] then x else Int(!x.negative, x.mag)
  }

  // Absolute value.
  function Abs(x: Int): (r: Int)
    requires Wf(x)
    ensures Wf(r)
    ensures IntValue(r) >= 0
    ensures IntValue(r) == if IntValue(x) < 0 then -IntValue(x) else IntValue(x)
  {
    Int(false, x.mag)
  }

  // Comparison: -1 / 0 / 1 for x < y / x == y / x > y.
  function Compare(x: Int, y: Int): (c: int)
    requires Wf(x) && Wf(y)
    ensures c == 0 <==> IntValue(x) == IntValue(y)
    ensures c < 0 <==> IntValue(x) < IntValue(y)
    ensures c > 0 <==> IntValue(x) > IntValue(y)
  {
    if !x.negative && !y.negative then
      BigNatAddSub.Compare(x.mag, y.mag)
    else if x.negative && y.negative then
      // both negative: order is reversed on magnitudes
      -BigNatAddSub.Compare(x.mag, y.mag)
    else if x.negative && !y.negative then
      // x < 0 <= y: x.mag != [] (Wf + negative), so IntValue(x) < 0 <= IntValue(y)
      NonEmptyMagPositive(x);
      -1
    else
      // x >= 0 > y
      NonEmptyMagPositive(y);
      1
  }

  // Addition, by sign case. Magnitudes combine with BigNat Add / Sub.
  function Add(x: Int, y: Int): (r: Int)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures IntValue(r) == IntValue(x) + IntValue(y)
  {
    if x.negative == y.negative then
      // same sign: add magnitudes, keep the sign
      Make(x.negative, BigNatAddSub.Add(x.mag, y.mag))
    else
      // opposite signs: subtract smaller magnitude from larger; sign follows larger
      var c := BigNatAddSub.Compare(x.mag, y.mag);
      if c == 0 then
        Zero
      else if c > 0 then
        // |x| > |y|: result has x's sign, magnitude |x|-|y|
        Make(x.negative, BigNatAddSub.Sub(x.mag, y.mag))
      else
        // |y| > |x|: result has y's sign, magnitude |y|-|x|
        Make(y.negative, BigNatAddSub.Sub(y.mag, x.mag))
  }

  // Subtraction via negation.
  function Sub(x: Int, y: Int): (r: Int)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures IntValue(r) == IntValue(x) - IntValue(y)
  {
    Add(x, Negate(y))
  }

  // Multiplication: magnitudes multiply, signs xor; zero stays canonical.
  function Mul(x: Int, y: Int): (r: Int)
    requires Wf(x) && Wf(y)
    ensures Wf(r)
    ensures IntValue(r) == IntValue(x) * IntValue(y)
  {
    var m := BigNatMul.Mul(x.mag, y.mag);
    MulSignValue(x, y, m);
    Make(x.negative != y.negative, m)
  }

  // Value(x.mag) * Value(y.mag) relates to IntValue(x) * IntValue(y) up to sign.
  lemma MulSignValue(x: Int, y: Int, m: seq<limb>)
    requires Value(m) == Value(x.mag) * Value(y.mag)
    ensures (if (x.negative != y.negative) then -(Value(m) as int) else Value(m) as int)
            == IntValue(x) * IntValue(y)
  {
    // Four sign cases; each is a * b with the sign pulled out.
  }
}

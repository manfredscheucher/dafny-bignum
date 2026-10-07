/*******************************************************************************
 * dafny-bignum / fixed-width: FwRealPrint
 *
 * Pure char / decimal-string helpers for FwReal.ToString, with NO fw import, so
 * the SMT context has no recursive bignum axioms. Mirrors src/PureArith's
 * DigitChar / ParseDec / DenotesDecimal, but is kept self-contained.
 *
 * The compiled surface (used from FwReal) is only `DigitCharM` and `Zeros`,
 * both of which are native (char / seq<char> / size_t lengths). ParseDec and
 * DenotesDecimal are ghost specs used to state correctness of the digit string.
 *******************************************************************************/

module FwRealPrint {

  // The character for a single decimal digit d (0..9). GHOST: used only in specs
  // (the executable digit char comes from indexing the constant "0123456789").
  ghost function DigitChar(d: nat): char
    requires d < 10
  {
    (d + ('0' as int)) as char
  }

  ghost predicate IsDigitChar(c: char)
  {
    '0' <= c <= '9'
  }

  ghost function DigitVal(c: char): nat
    requires IsDigitChar(c)
  {
    (c as int) - ('0' as int)
  }

  lemma DigitRoundTrip(d: nat)
    requires d < 10
    ensures IsDigitChar(DigitChar(d)) && DigitVal(DigitChar(d)) == d
  {}

  // The nat a digit string denotes, most-significant digit first.
  ghost function ParseDec(s: seq<char>): nat
    requires forall i :: 0 <= i < |s| ==> IsDigitChar(s[i])
  {
    if |s| == 0 then 0
    else ParseDec(s[..|s| - 1]) * 10 + DigitVal(s[|s| - 1])
  }

  // s is a nonempty string of digits denoting n (no canonical-form constraint
  // here — leading zeros are allowed, which the ToString layout can produce).
  ghost predicate AllDigits(s: seq<char>)
  {
    forall i :: 0 <= i < |s| ==> IsDigitChar(s[i])
  }

  // ParseDec of a one-element digit string is that digit.
  lemma ParseDecSingle(c: char)
    requires IsDigitChar(c)
    ensures AllDigits([c]) && ParseDec([c]) == DigitVal(c)
  {
    assert [c][..0] == [];
  }

}

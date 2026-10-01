/*******************************************************************************
 * dafny-bignum: BigNatConv
 *
 * Conversion into the limb representation: build a BigNat from a Dafny nat,
 * proved against Value(). This direction needs only the core. (The reverse
 * decimal rendering needs repeated division by 10 and is not provided here.)
 *******************************************************************************/

include "BigNat.dfy"

module BigNatConv {
  import opened BigNat

  // Build normalized limbs from a nat. Least significant limb first.
  function FromNat(n: nat): (xs: seq<limb>)
    ensures Normalized(xs)
    ensures Value(xs) == n
    decreases n
  {
    if n == 0 then []
    else
      assert n % BASE < BASE;
      var head: limb := (n % BASE) as limb;
      var tail := FromNat(n / BASE);
      FromNatStep(n, head, tail);
      [head] + tail
  }

  // Value of the assembled sequence equals n, and it stays normalized.
  lemma FromNatStep(n: nat, head: limb, tail: seq<limb>)
    requires n > 0
    requires head == (n % BASE) as limb
    requires Value(tail) == n / BASE && Normalized(tail)
    ensures Value([head] + tail) == n
    ensures Normalized([head] + tail)
  {
    assert ([head] + tail)[0] == head;
    assert ([head] + tail)[1..] == tail;
    calc {
      Value([head] + tail);
      L(head) + BASE * Value(tail);
      (n % BASE) + BASE * (n / BASE);
      { DivModId(n, BASE); }
      n;
    }
    // Normalized: either tail is nonempty (its last limb is the last limb of the
    // whole sequence and is nonzero), or tail is empty and head != 0 because
    // n > 0 and n < BASE would give head == n != 0; if n >= BASE then tail != [].
    if tail == [] {
      assert n / BASE == 0;
      assert n < BASE;
      assert head == n as limb;
      assert n > 0;
    }
  }

  // n == (n % b) + b * (n / b) for b > 0.
  lemma DivModId(n: nat, b: nat)
    requires b > 0
    ensures n == (n % b) + b * (n / b)
  {}
}

/*******************************************************************************
 * dafny-bignum / fixed-width: FwTest
 *
 * Regression checks for the fixed-width stack. Concrete limb sequences are run
 * through the real methods and the ghost Value() of each result is asserted at
 * verification time (so `Dafny verify` IS the test). Numbers are built as limb
 * literals (base 2^32): [a] is a, [a, b] is a + b*2^32, etc.
 *
 * Also a Main so the stack can be run (and, via `translate cpp`, shown to be
 * Boost-free end to end).
 *******************************************************************************/

include "FwNat.dfy"
include "FwSub.dfy"
include "FwMul.dfy"
include "FwCompare.dfy"
include "FwDivMod.dfy"
include "FwGCD.dfy"

module FwTest {
  import opened FwNat
  import FwSub
  import FwMul
  import FwCompare
  import FwDivMod
  import FwGCD

  // Addition: 5 + 7 == 12 (single limb, no carry).
  method TestAddSmall() {
    var zs, cout := AddSeq([5 as limb], [7 as limb], 0);
    assert Value([5 as limb]) == 5;
    assert Value([7 as limb]) == 7;
    assert Value(zs) + (cout as nat) * Pow32(1) == 12;
    assert cout == 0;
    assert Value(zs) == 12;
  }

  // Addition with carry across the limb boundary:
  // (2^32 - 1) + 1 == 2^32  ->  low limb 0, carry 1.
  method TestAddCarry() {
    var maxlimb := 0xFFFF_FFFF as limb;
    var zs, cout := AddSeq([maxlimb], [1 as limb], 0);
    assert Value([maxlimb]) == 0xFFFF_FFFF;
    assert Value(zs) + (cout as nat) * Pow32(1) == 0x1_0000_0000;
  }

  // Subtraction: 2^32 - 1 == (2^32 - 1), spanning two limbs minus one.
  method TestSub() {
    // xs = 2^32 (== [0, 1]), ys = 1 (== [1, 0]); both length 2
    var zs, bout := FwSub.SubSeq([0 as limb, 1 as limb], [1 as limb, 0 as limb], 0);
    assert Value([0 as limb, 1 as limb]) == 0x1_0000_0000;
    assert Value([1 as limb, 0 as limb]) == 1;
    // SubSeq's spec: Value(xs) + bout*Pow32(2) == Value(ys) + bin + Value(zs).
    // With Value(xs)=2^32, Value(ys)=1, bin=0, the difference is 2^32-1 (bout=0).
    assert 0x1_0000_0000 + (bout as nat) * Pow32(2) == 1 + 0 + Value(zs);
  }

  // Multiplication: (2^32 - 1) * (2^32 - 1), overflows one limb.
  method TestMul() {
    var m := 0xFFFF_FFFF as limb;
    var zs := FwMul.Mul([m], [m]);
    assert Value([m]) == 0xFFFF_FFFF;
    assert Value(zs) == 0xFFFF_FFFF * 0xFFFF_FFFF;
  }

  // Comparison across the sign-free magnitudes.
  method TestCompare() {
    var c1 := FwCompare.Compare([1 as limb], [2 as limb]);
    assert c1 < 0;
    var c2 := FwCompare.Compare([0 as limb, 1 as limb], [5 as limb]);  // 2^32 vs 5
    assert c2 > 0;
    var c3 := FwCompare.Compare([7 as limb], [7 as limb]);
    assert c3 == 0;
  }

  // Division: 100 / 7 == 14 remainder 2.
  method TestDivMod() {
    var q, r := FwDivMod.DivMod([100 as limb], [7 as limb]);
    assert Value([100 as limb]) == 100;
    assert Value([7 as limb]) == 7;
    assert Value([100 as limb]) == Value(q) * Value([7 as limb]) + Value(r);
    assert Value(r) < 7;
    assert Value(q) == 14 && Value(r) == 2;
  }

  // gcd(12, 18) == 6.
  method TestGcd() {
    var g := FwGCD.GCD([12 as limb], [18 as limb]);
    assert Value([12 as limb]) == 12;
    assert Value([18 as limb]) == 18;
    assert FwGCD.IsGCD(Value(g), 12, 18);
  }

  // Runnable end-to-end: compute and print a few results. Exercises the native
  // (Boost-free) generated code.
  // Runnable end-to-end check. Compares each result to the expected limb
  // sequence with `expect` (a runtime assertion that aborts with a message on
  // failure) and prints a status line. No `x as int` conversions in print, so
  // the generated C++ needs no `_dafny` module object — it builds Boost-free
  // with a plain g++ (see fw/README).
  method Main() {
    // 5 + 7 == 12 (single limb, no carry)
    var sum, c := AddSeq([5 as limb], [7 as limb], 0);
    expect sum == [12 as limb] && c == 0;
    print "add  5 + 7            = [12]            OK\n";

    // (2^32-1)^2 == 0xFFFFFFFE00000001 == limbs [1, 0xFFFFFFFE, 0]
    var prod := FwMul.Mul([0xFFFF_FFFF as limb], [0xFFFF_FFFF as limb]);
    expect prod == [1 as limb, 0xFFFF_FFFE as limb];
    print "mul  (2^32-1)^2       = [1, 4294967294] OK\n";

    // 100 / 7 == 14 remainder 2
    var q, r := FwDivMod.DivMod([100 as limb], [7 as limb]);
    expect q == [14 as limb] && r == [2 as limb];
    print "div  100 / 7          = q[14] r[2]      OK\n";

    // gcd(12, 18) == 6
    var g := FwGCD.GCD([12 as limb], [18 as limb]);
    expect g == [6 as limb];
    print "gcd  12, 18           = [6]             OK\n";

    print "all fixed-width checks passed\n";
  }
}

/*******************************************************************************
 * dafny-bignum: demo
 *
 * Small runnable program exercising the verified unsigned operations. Builds
 * numbers from nats, adds / subtracts / multiplies them, and prints the limb
 * sequences. Translatable to any Dafny target (C++, C#, Java, Go, Python, JS):
 *
 *   dafny run examples/demo.dfy
 *   dafny build -t:cs examples/demo.dfy      # etc.
 *******************************************************************************/

include "../src/BigNat.dfy"
include "../src/BigNatConv.dfy"
include "../src/BigNatAddSub.dfy"
include "../src/BigNatMul.dfy"

module Demo {
  import opened BigNat
  import opened BigNatConv
  import opened BigNatAddSub
  import opened BigNatMul

method PrintLimbs(tag: string, xs: seq<limb>)
{
  print tag, " = limbs[";
  var i := 0;
  while i < |xs| {
    if i > 0 { print ", "; }
    print xs[i] as int;
    i := i + 1;
  }
  print "]  (value ", Value(xs), ")\n";
}

method Main()
{
  // Numbers large enough to span several 32-bit limbs.
  var a := FromNat(123456789012345678901234567890);
  var b := FromNat(987654321098765432109876543210);

  PrintLimbs("a", a);
  PrintLimbs("b", b);

  var sum := Add(a, b);
  PrintLimbs("a + b", sum);

  var prod := Mul(a, b);
  PrintLimbs("a * b", prod);

  // Sub needs Value(b) <= Value(a); b > a here, so subtract the other way.
  var diff := Sub(b, a);
  PrintLimbs("b - a", diff);

  print "\nchecks:\n";
  print "  value(a+b) == ", Value(a) + Value(b), " ? ", Value(sum) == Value(a) + Value(b), "\n";
  print "  value(a*b) == ", Value(a) * Value(b), " ? ", Value(prod) == Value(a) * Value(b), "\n";
  print "  value(b-a) == ", Value(b) - Value(a), " ? ", Value(diff) == Value(b) - Value(a), "\n";
}
}

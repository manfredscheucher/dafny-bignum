/*******************************************************************************
 * dafny-bignum / fixed-width: FwMul
 *
 * Fixed-width schoolbook multiplication on top of FwNat. Same hard rule: every
 * executable value is a fixed-width newtype (limb/dword); int/nat only in ghost
 * specs and lemmas. A single-limb product limb*limb (+carry) fits in a dword:
 * (2^32-1)^2 + (2^32-1) < 2^64, so it never overflows uint64.
 *******************************************************************************/

include "FwNat.dfy"
include "FwDivMod.dfy"

module FwMul {
  import opened FwNat
  import FwDivMod

  //////////////////////////////////////////////////////////////////////////////
  // Single-limb multiply-accumulate column.
  //////////////////////////////////////////////////////////////////////////////

  // Compute x*m + carry, split into (lo, hi) with x*m+carry == hi*BASE + lo.
  // hi < BASE holds because x*m+carry <= (2^32-1)^2 + (2^32-1) < 2^64, and the
  // quotient by 2^32 of a value < 2^64 is < 2^32.
  method MulAddColumn(x: limb, m: limb, carry: limb) returns (lo: limb, hi: limb)
    ensures (x as nat) * (m as nat) + (carry as nat)
         == (hi as nat) * 0x1_0000_0000 + (lo as nat)
  {
    // Bound the product so the dword arithmetic is in range: x,m,carry < 2^32,
    // so x*m + carry <= (2^32-1)^2 + (2^32-1) = 2^64 - 2^32 < 2^64.
    ColumnBound(x as nat, m as nat, carry as nat);
    var xm: dword := (x as dword) * (m as dword);
    var p: dword := xm + (carry as dword);
    lo := (p % BASE) as limb;
    hi := (p / BASE) as limb;
    // p as nat == x*m + carry (the casts preserve value; dword holds it)
    assert (p as nat) == (x as nat) * (m as nat) + (carry as nat);
    // Euclidean split of p by BASE
    assert (p as nat) == (hi as nat) * 0x1_0000_0000 + (lo as nat);
  }

  // x,m,carry each < 2^32  ==>  x*m < 2^64  and  x*m + carry < 2^64.
  lemma ColumnBound(x: nat, m: nat, carry: nat)
    requires x < 0x1_0000_0000 && m < 0x1_0000_0000 && carry < 0x1_0000_0000
    ensures x * m < 0x1_0000_0000_0000_0000
    ensures x * m + carry < 0x1_0000_0000_0000_0000
  {
    var N: nat := 0x1_0000_0000;
    // x <= N-1 and m <= N-1, so x*m <= (N-1)^2 = N^2 - 2N + 1
    MulMonoBoth(x, m, N - 1, N - 1);
    assert x * m <= (N - 1) * (N - 1);
    assert (N - 1) * (N - 1) == N * N - 2 * N + 1;
    assert N * N == 0x1_0000_0000_0000_0000;
    // x*m + carry <= N^2 - 2N + 1 + (N-1) = N^2 - N < N^2
    assert x * m + carry <= (N - 1) * (N - 1) + (N - 1);
  }

  // a<=c && b<=d ==> a*b <= c*d  (for nats).
  lemma MulMonoBoth(a: nat, b: nat, c: nat, d: nat)
    requires a <= c && b <= d
    ensures a * b <= c * d
  {
    MulMonoRight(a, b, d);   // a*b <= a*d
    MulMonoLeft(a, c, d);    // a*d <= c*d
  }

  lemma MulMonoRight(a: nat, b: nat, d: nat)
    requires b <= d
    ensures a * b <= a * d
  {}

  lemma MulMonoLeft(a: nat, c: nat, d: nat)
    requires a <= c
    ensures a * d <= c * d
  {}

  //////////////////////////////////////////////////////////////////////////////
  // Multiply a limb sequence by a single limb: Value(zs) == Value(xs) * m.
  //////////////////////////////////////////////////////////////////////////////

  method MulLimb(xs: seq<limb>, m: limb) returns (zs: seq<limb>)
    ensures Value(zs) == Value(xs) * (m as nat)
    decreases |xs|
  {
    zs := MulLimbCarry(xs, m, 0);
  }

  // Value(zs) == Value(xs) * m + carry. Returns a sequence of length |xs|+1 so
  // the final carry fits. The low |xs| limbs plus a top carry limb.
  method MulLimbCarry(xs: seq<limb>, m: limb, carry: limb) returns (zs: seq<limb>)
    ensures Value(zs) == Value(xs) * (m as nat) + (carry as nat)
    ensures |zs| == |xs| + 1
    decreases |xs|
  {
    if |xs| == 0 {
      zs := [carry];
      assert Value([carry]) == (carry as nat);
      return;
    }
    var lo, hi := MulAddColumn(xs[0], m, carry);
    var rest := MulLimbCarry(xs[1..], m, hi);
    zs := [lo] + rest;
    MulLimbStep(xs, m, carry, lo, hi, rest, zs);
  }

  // Proof of the recursive step of MulLimbCarry. All ghost / nat arithmetic.
  // Given: xs[0]*m + carry == hi*B + lo              (column identity)
  //        Value(rest) == Value(xs[1..])*m + hi      (recursive hypothesis)
  //        zs == [lo] + rest
  // Show:  Value(zs) == Value(xs)*m + carry
  lemma MulLimbStep(xs: seq<limb>, m: limb, carry: limb,
                    lo: limb, hi: limb, rest: seq<limb>, zs: seq<limb>)
    requires |xs| > 0
    requires (xs[0] as nat) * (m as nat) + (carry as nat)
          == (hi as nat) * 0x1_0000_0000 + (lo as nat)
    requires Value(rest) == Value(xs[1..]) * (m as nat) + (hi as nat)
    requires zs == [lo] + rest
    ensures Value(zs) == Value(xs) * (m as nat) + (carry as nat)
  {
    assert zs[0] == lo && zs[1..] == rest;
    var B: nat := 0x1_0000_0000;
    var vm := m as nat;
    var vlo := lo as nat; var vhi := hi as nat; var vcarry := carry as nat;
    var vx0 := xs[0] as nat; var vxt := Value(xs[1..]);
    // Value unfolds on the head
    assert Value(xs) == vx0 + B * vxt;
    assert Value(zs) == vlo + B * Value(rest);
    // substitute the recursive hypothesis
    assert Value(rest) == vxt * vm + vhi;
    // Value(zs) == vlo + B*(vxt*vm + vhi) == vlo + B*vhi + B*(vxt*vm)
    MulLimbAlgebra(B, vm, vlo, vhi, vcarry, vx0, vxt);
  }

  // The nonlinear algebra of MulLimbStep, over plain nats, products named once.
  //   given  vx0*vm + vcarry == vhi*B + vlo
  //   show   vlo + B*(vxt*vm + vhi) == (vx0 + B*vxt)*vm + vcarry
  lemma MulLimbAlgebra(B: nat, vm: nat, vlo: nat, vhi: nat, vcarry: nat,
                       vx0: nat, vxt: nat)
    requires vx0 * vm + vcarry == vhi * B + vlo
    ensures vlo + B * (vxt * vm + vhi) == (vx0 + B * vxt) * vm + vcarry
  {
    // LHS = vlo + B*vhi + B*(vxt*vm)
    //     = (vx0*vm + vcarry)   [since vlo + B*vhi == vx0*vm + vcarry]
    //       + B*(vxt*vm)
    //     = vx0*vm + B*vxt*vm + vcarry
    //     = (vx0 + B*vxt)*vm + vcarry
    calc {
      vlo + B * (vxt * vm + vhi);
      { assert B * (vxt * vm + vhi) == B * (vxt * vm) + B * vhi; }
      vlo + B * (vxt * vm) + B * vhi;
      { assert vlo + B * vhi == vx0 * vm + vcarry; }
      vx0 * vm + B * (vxt * vm) + vcarry;
      { assert B * (vxt * vm) == (B * vxt) * vm; }
      vx0 * vm + (B * vxt) * vm + vcarry;
      { assert vx0 * vm + (B * vxt) * vm == (vx0 + B * vxt) * vm; }
      (vx0 + B * vxt) * vm + vcarry;
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Shift by whole limbs: prepend k zero limbs. Value scales by Pow32(k).
  //////////////////////////////////////////////////////////////////////////////

  // Shift left by exactly one limb: prepend a zero limb. Value scales by 2^32.
  // (Mul only ever needs a one-limb shift per recursion step.) No numeric
  // parameter, so nothing unbounded enters compiled code.
  method ShiftOne(xs: seq<limb>) returns (zs: seq<limb>)
    ensures Value(zs) == Value(xs) * 0x1_0000_0000
  {
    zs := [0 as limb] + xs;
    assert zs[0] == 0 as limb && zs[1..] == xs;
    assert Value(zs) == 0 + 0x1_0000_0000 * Value(xs);
    assert 0x1_0000_0000 * Value(xs) == Value(xs) * 0x1_0000_0000;
  }

  //////////////////////////////////////////////////////////////////////////////
  // Full multiplication: schoolbook over ys, shift-and-add.
  //////////////////////////////////////////////////////////////////////////////

  // Add two sequences (any lengths) returning the exact sum (no length cap).
  // Value(zs) == Value(xs) + Value(ys). Built on AddSeq after zero-padding to a
  // common length, plus a possible top carry limb.
  method AddFull(xs: seq<limb>, ys: seq<limb>) returns (zs: seq<limb>)
    ensures Value(zs) == Value(xs) + Value(ys)
  {
    // Pad the shorter to the longer by recursing on the two sequences together
    // (no free numeric counter -> nothing unbounded in compiled code).
    var xp, yp := PadEqual(xs, ys);
    var s, cout := AddSeq(xp, yp, 0);
    zs := s + [cout];
    AddFullStep(xp, yp, s, cout, zs, |xp|);
  }

  // Zero-pad the shorter of xs, ys so both have equal length; Values unchanged.
  method PadEqual(xs: seq<limb>, ys: seq<limb>)
      returns (xp: seq<limb>, yp: seq<limb>)
    ensures |xp| == |yp|
    ensures Value(xp) == Value(xs) && Value(yp) == Value(ys)
    decreases |xs| + |ys|
  {
    if |xs| == 0 && |ys| == 0 {
      xp, yp := xs, ys;
    } else if |xs| == 0 {
      // xs empty, ys not: pad xs with a zero head, keep ys's head.
      var xr, yr := PadEqual([], ys[1..]);
      xp := [0 as limb] + xr;
      yp := [ys[0]] + yr;
      HeadZero(xr, xp);                  // Value(xp) == Value([]) == 0 (via B*Value(xr), xr all accounts 0)
      HeadSplice(ys, yr, yp);            // Value(yp) == Value(ys)
    } else if |ys| == 0 {
      var xr, yr := PadEqual(xs[1..], []);
      xp := [xs[0]] + xr;
      yp := [0 as limb] + yr;
      HeadSplice(xs, xr, xp);
      HeadZero(yr, yp);
    } else {
      var xr, yr := PadEqual(xs[1..], ys[1..]);
      xp := [xs[0]] + xr;
      yp := [ys[0]] + yr;
      HeadSplice(xs, xr, xp);
      HeadSplice(ys, yr, yp);
    }
  }

  // Prepending s's own head to a remainder with s's tail-Value gives Value(s).
  lemma HeadSplice(s: seq<limb>, r: seq<limb>, p: seq<limb>)
    requires |s| > 0
    requires Value(r) == Value(s[1..])
    requires p == [s[0]] + r
    ensures Value(p) == Value(s)
  {
    assert p[0] == s[0] && p[1..] == r;
    assert Value(p) == (s[0] as nat) + 0x1_0000_0000 * Value(r);
    assert Value(s) == (s[0] as nat) + 0x1_0000_0000 * Value(s[1..]);
  }

  // Prepending a zero head to a zero-Value remainder gives Value 0.
  lemma HeadZero(r: seq<limb>, p: seq<limb>)
    requires Value(r) == 0
    requires p == [0 as limb] + r
    ensures Value(p) == 0
  {
    assert p[0] == 0 as limb && p[1..] == r;
    assert Value(p) == 0 + 0x1_0000_0000 * Value(r);
  }

  // Value(s + [cout]) == Value(s) + cout*Pow32(n) == Value(xp)+Value(yp).
  lemma AddFullStep(xp: seq<limb>, yp: seq<limb>, s: seq<limb>, cout: limb,
                    zs: seq<limb>, n: nat)
    requires |xp| == |yp| == n == |s|
    requires Value(xp) + Value(yp) == Value(s) + (cout as nat) * Pow32(n)
    requires zs == s + [cout]
    ensures Value(zs) == Value(xp) + Value(yp)
  {
    AppendLimbValue(s, cout);
    assert Value(zs) == Value(s) + (cout as nat) * Pow32(|s|);
  }

  // Value(s + [c]) == Value(s) + c*Pow32(|s|).
  lemma AppendLimbValue(s: seq<limb>, c: limb)
    ensures Value(s + [c]) == Value(s) + (c as nat) * Pow32(|s|)
    decreases |s|
  {
    var B: nat := 0x1_0000_0000;
    if |s| == 0 {
      assert s + [c] == [c];
      assert Value([c]) == (c as nat);
      assert Pow32(0) == 1;
    } else {
      assert (s + [c])[0] == s[0];
      assert (s + [c])[1..] == s[1..] + [c];
      AppendLimbValue(s[1..], c);
      // Value(s+[c]) == s[0] + B*Value(s[1..]+[c])
      //             == s[0] + B*(Value(s[1..]) + c*Pow32(|s|-1))
      //             == Value(s) + B*c*Pow32(|s|-1) == Value(s) + c*Pow32(|s|)
      assert Pow32(|s|) == B * Pow32(|s| - 1);
      AppendAlgebra(B, s[0] as nat, Value(s[1..]), c as nat, Pow32(|s| - 1));
    }
  }

  //   show s0 + B*(vt + c*pk1) == (s0 + B*vt) + c*(B*pk1)
  lemma AppendAlgebra(B: nat, s0: nat, vt: nat, c: nat, pk1: nat)
    ensures s0 + B * (vt + c * pk1) == (s0 + B * vt) + c * (B * pk1)
  {
    calc {
      s0 + B * (vt + c * pk1);
      { assert B * (vt + c * pk1) == B * vt + B * (c * pk1); }
      s0 + B * vt + B * (c * pk1);
      { assert B * (c * pk1) == c * (B * pk1); }
      (s0 + B * vt) + c * (B * pk1);
    }
  }

  // Schoolbook multiply: Value(zs) == Value(xs) * Value(ys).
  // Recurse on ys: xs*ys = xs*ys[0] + B*(xs*ys[1..]).
  method Mul(xs: seq<limb>, ys: seq<limb>) returns (zs: seq<limb>)
    ensures Value(zs) == Value(xs) * Value(ys)
    ensures Normalized(zs)
    decreases |ys|
  {
    if |ys| == 0 {
      zs := [];
      assert Value([]) == 0;
      assert Value(xs) * Value(ys) == Value(xs) * 0;
      return;
    }
    // partial = xs * ys[0]
    var partial := MulLimb(xs, ys[0]);
    // tail = xs * ys[1..]
    var tail := Mul(xs, ys[1..]);
    // shifted = tail << 1 limb  (Value * B)
    var shifted := ShiftOne(tail);
    zs := AddFull(partial, shifted);
    MulStep(xs, ys, partial, tail, shifted, zs);
    // AddFull always appends a carry limb, so zs may carry leading zero limbs
    // (e.g. an all-zero product). Normalize to drop them; Value is preserved.
    zs := FwDivMod.Normalize(zs);
  }

  // Value(zs) == Value(xs)*Value(ys) from the pieces.
  //   partial == Value(xs)*ys[0]
  //   tail    == Value(xs)*Value(ys[1..])
  //   shifted == tail * B
  //   zs      == partial + shifted
  lemma MulStep(xs: seq<limb>, ys: seq<limb>, partial: seq<limb>,
                tail: seq<limb>, shifted: seq<limb>, zs: seq<limb>)
    requires |ys| > 0
    requires Value(partial) == Value(xs) * (ys[0] as nat)
    requires Value(tail) == Value(xs) * Value(ys[1..])
    requires Value(shifted) == Value(tail) * 0x1_0000_0000
    requires Value(zs) == Value(partial) + Value(shifted)
    ensures Value(zs) == Value(xs) * Value(ys)
  {
    var B: nat := 0x1_0000_0000;
    var vx := Value(xs);
    var vy0 := ys[0] as nat;
    var vyt := Value(ys[1..]);
    // Value(ys) == ys[0] + B*Value(ys[1..])
    assert Value(ys) == vy0 + B * vyt;
    // Value(zs) == vx*vy0 + (vx*vyt)*B
    assert Value(shifted) == (vx * vyt) * B;
    MulFullAlgebra(B, vx, vy0, vyt);
  }

  //   show vx*vy0 + (vx*vyt)*B == vx*(vy0 + B*vyt)
  lemma MulFullAlgebra(B: nat, vx: nat, vy0: nat, vyt: nat)
    ensures vx * vy0 + (vx * vyt) * B == vx * (vy0 + B * vyt)
  {
    calc {
      vx * vy0 + (vx * vyt) * B;
      { assert (vx * vyt) * B == vx * (vyt * B); }
      vx * vy0 + vx * (vyt * B);
      { assert vx * vy0 + vx * (vyt * B) == vx * (vy0 + vyt * B); }
      vx * (vy0 + vyt * B);
      { assert vyt * B == B * vyt; }
      vx * (vy0 + B * vyt);
    }
  }
}

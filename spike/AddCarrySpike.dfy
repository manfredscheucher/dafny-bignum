// Spike: can a single bignum operation be written with FIXED-WIDTH limbs so the
// C++ backend generates native uint32/uint64 code with NO BigNumber (Boost)?
//
// The verified library computes carries in Dafny `int` (unbounded), which the
// C++ backend turns into `BigNumber` = Boost cpp_int. To actually REPLACE Boost,
// the executable arithmetic must stay in types that carry a NativeType, so the
// generator emits uint32/uint64 instead of BigNumber.
//
// Here: limb = uint32-ranged newtype, carry/sum computed in a uint64-ranged
// newtype. No `int`/`nat` appears in the executable method body (only in ghost
// specs). If the generated C++ is BigNumber-free, the approach is viable.

// A 32-bit limb. Dafny gives this NativeType uint32 (smallest type that fits).
newtype limb = x: int | 0 <= x < 0x1_0000_0000

// A 64-bit intermediate. NativeType uint64. Holds limb+limb+carry (max
// 2*(2^32-1)+1 < 2^64) and a single-limb product (< 2^64).
newtype u64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

const BASE: u64 := 0x1_0000_0000

// Add two limbs with an incoming carry bit, fixed width throughout.
// Returns (low limb, carry-out bit). Proved against the integer identity.
method AddLimb(a: limb, b: limb, cin: limb) returns (lo: limb, cout: limb)
  requires cin == 0 || cin == 1
  ensures cout == 0 || cout == 1
  // the mathematical fact, stated over int via the limbs' values:
  ensures (a as int) + (b as int) + (cin as int) == (cout as int) * 0x1_0000_0000 + (lo as int)
{
  // widen to 64 bits; the sum cannot overflow u64
  var s: u64 := (a as u64) + (b as u64) + (cin as u64);
  lo := (s % BASE) as limb;
  cout := (s / BASE) as limb;
}

# dafny-bignum

Arbitrary-precision integers and rationals, written and **verified in pure
Dafny**. Every operation is proved correct against its mathematical value, and
the code translates to any Dafny target (C++, C#, Java, Go, Python, JS) with no
external big-integer dependency.

The motivation is the Dafny C++ backend, which otherwise needs Boost or GMP for
its `int`/`real` runtime types. Here the big-integer logic is just verified
Dafny code instead.

## Representation

- `BigNat` — unsigned, little-endian sequence of `bv32` limbs, base `2^32`,
  normalized (no leading zero limb, `[]` is zero).
- `BigInt` — sign + magnitude over `BigNat`.
- `Rational` — `num`/`den` over `BigInt`, kept in lowest terms via gcd.

Correctness is stated against `Value()` (the nat a limb sequence denotes) — e.g.
`Value(Add(x, y)) == Value(x) + Value(y)`.

## Layout

    src/        the library (BigNat, BigNatAddSub, BigNatMul, BigNatDivMod, BigInt, Rational)
    test/       verified test lemmas + runnable checks
    examples/   Main programs, translatable to C++ etc.
    doc/SPEC.md  what was asked for and why it was built this way
    scripts/verify.sh  verify the whole src/ tree

## Verify

    ./scripts/verify.sh

Requires a `dafny` on PATH (developed against 4.11).

## Status

Core representation is verified. Add/Sub/Compare and Mul are in progress;
DivMod (long division) is the hard proof and comes next; signed `BigInt` + gcd
and `Rational` sit on top. See `doc/SPEC.md`.

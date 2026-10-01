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

Verified: BigNat core, Compare/Add/Sub, Mul, DivMod (recursive binary long
division), Euclidean gcd, FromNat, and signed `BigInt` (add/sub/mul/compare/
negate/abs). `Rational` (num/den, gcd-reduced) sits on top. `scripts/verify.sh`
checks the whole tree with no `assume`/`axiom`. See `doc/SPEC.md`.

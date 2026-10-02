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

All verified (`scripts/verify.sh`, 0 errors, no `assume`/`axiom`): BigNat core,
Compare/Add/Sub, Mul, DivMod (recursive binary long division), Euclidean gcd,
FromNat, signed `BigInt` (add/sub/mul/compare/negate/abs), and `Rational`
(add/sub/mul/compare, gcd-reduced) against a `real` value. Regression tests and
a runnable demo included.

Not done: the Phase-2 step that actually removes the Boost dependency (rewriting
the internals to fixed-width `uint64` instead of Dafny's unbounded `nat`). See
the open items in `doc/SPEC.md` — this is the real test of the whole idea.

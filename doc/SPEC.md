# dafny-bignum — specification & decision log

This file records what was asked for and which decisions were made, so the work
can be re-checked later (by the author, by me, or by a fresh reviewer with no
context).

## Origin / motivation

The Dafny C++ backend currently relies on an external big-integer library
(Boost.Multiprecision `cpp_int`, previously GMP) for its runtime `int` / `real`
types. See `dafny/_private/cpp/BIGNUM_BACKEND.md`. The idea behind this repo:

> Instead of pulling in Boost/GMP, write an arbitrary-precision integer
> implementation **in Dafny itself**, and *verify it*. The core operations are
> well understood, there is plenty of reference code to follow, and a verified
> implementation removes the external-dependency (the "C++ boost dilemma").
> Rationals ("reals" in Dafny) need gcd to keep representatives small.

The user explicitly asked for this to live in its own repo:
`git@github.com:manfredscheucher/dafny-bignum.git`.

## What this is (and is not)

**Phase 1 (this repo): a standalone, verified arbitrary-precision library in
pure Dafny.** Translatable to any Dafny target (C++, C#, Java, Go, Python, JS),
correctness proved against a mathematical `Value()` spec. Self-contained — it
does not depend on Dafny's own built-in `int` inside its representation.

**Not (yet) phase 2: dropping it into `DafnyRuntime.h` to replace Boost at the
runtime level.** That is a separate, larger effort (ABI, making sequence
lengths/indices bv-based rather than the runtime `DafnyInt`, and performance vs.
a tuned C++ library). This library is built so as not to foreclose that path
(bv32 limbs, no dependency on Dafny `int` internally), but it is not promised to
be a drop-in Boost replacement without that second phase. This distinction was
made explicit to the user before building.

## Design decisions

| Decision | Choice | Why |
|---|---|---|
| Not modular bignum | plain signed arbitrary-precision int | The user's need is Dafny's `int` semantics (unbounded signed), not fixed-modulus/constant-time crypto. A separate modular-bigint project exists and is explicitly out of scope. |
| Limb type | `bv32`, base `2^32` | A single-limb product fits exactly in `bv64` (2^32·2^32 = 2^64), so the multiplication proof needs no 128-bit reasoning. Chosen over bv64 for provability first; bv64 is a phase-2 speed option. |
| Representation | little-endian `seq<limb>`, LSB first, normalized (no leading zero limb) | Unique representation, `[]` is canonical zero. Mirrors Dafny stdlib `LittleEndianNat`. |
| Proof approach | build on the structure of `Std.Arithmetic.LittleEndianNat` | Proven lemma structure (ToNat, SeqAdd/SeqSub carry/borrow) reused, rewritten for concrete bv32 limbs and our `Value()` spec. Far less proof risk than from scratch. |
| Repo name | `dafny-bignum` | Covers the integer core; Rational sits on top. |

## Module map

- `src/BigNat.dfy` — representation core. `Value`, `Normalize`, `Pow2_32`,
  `ValueBound`, `ValueAppend`, zero-uniqueness. **Verified.**
- `src/BigNatAddSub.dfy` — `Add`, `Sub`, `Compare` vs `Value()`.
- `src/BigNatMul.dfy` — schoolbook `Mul` vs `Value()`.
- `src/BigNatDivMod.dfy` — Euclidean division/modulo (the hardest proof).
- `src/BigInt.dfy` — signed wrapper (sign + magnitude) + `GCD`.
- `src/Rational.dfy` — `num`/`den` over `BigInt`, gcd-reduced.

## Scope: minimal, not fast

Explicitly **no performance work**. No Karatsuba/Toom multiplication, no
Newton/Knuth-D division, no limb-level micro-optimisation. Only the minimum an
arbitrary-precision int + rational needs: schoolbook add/sub/mul, plain long
division, Euclidean gcd, gcd-reduced rationals. Simple and verifiable beats
fast. Speed is a possible phase-2 concern, deliberately out of scope here.

## Verification contract

Every operation carries a postcondition stated in terms of `Value()` (or, for
signed, the mathematical integer it denotes). No `assume`, no `{:axiom}`, no
proof-suppressing `assert`. `scripts/verify.sh` verifies the whole `src/` tree.

## Open items / TODO

- DivMod full proof (long division quotient estimation) — the known hard part.
- Phase-2 runtime integration is out of scope here.

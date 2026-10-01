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
| Limb type | `newtype limb = i:int \| 0 <= i < 2^32`, base `2^32` | **Revised from `bv32`.** The bv32 choice forced bit-vector↔nat casts in every carry/borrow/mul step, and Z3 times out on those casts even in isolation (see `test/nat_limb_feasibility.dfy`). A nat-backed limb makes all carry logic plain nat arithmetic (`% BASE`, `/ BASE`) — cheap for Z3 and exactly what Dafny's own `Std.Arithmetic.LittleEndianNat` does (`digit = i:nat \| 0 <= i < BASE()`). Products are just nats (`x*m+c`), so no 64-bit fit is needed. Translates to a native 32-bit integer in C++. |
| Representation | little-endian `seq<limb>`, LSB first, normalized (no leading zero limb) | Unique representation, `[]` is canonical zero. Mirrors Dafny stdlib `LittleEndianNat`. |
| Proof approach | build on the structure of `Std.Arithmetic.LittleEndianNat` | Proven lemma structure (ToNat, SeqAdd/SeqSub carry/borrow) reused, rewritten for concrete bv32 limbs and our `Value()` spec. Far less proof risk than from scratch. |
| Repo name | `dafny-bignum` | Covers the integer core; Rational sits on top. |

## Module map

- `src/BigNat.dfy` — representation core. `Value`, `Normalize`, `Pow2_32`,
  `ValueBound`, `ValueAppend`, zero-uniqueness. **Verified (22).**
- `src/BigNatAddSub.dfy` — `Add`, `Sub`, `Compare` vs `Value()`. **Verified (35).**
- `src/BigNatMul.dfy` — schoolbook `Mul` vs `Value()`. **Verified (39).**
- `src/BigNatDivMod.dfy` — division/modulo by recursive binary long division,
  `Value(xs) == Value(q)*Value(ys) + Value(r)`, `Value(r) < Value(ys)`. The
  hardest proof. **Verified (67).**
- `src/BigNatGCD.dfy` — Euclidean gcd, proved against a mathematical `IsGCD`
  predicate. **Verified (16).**
- `src/BigNatConv.dfy` — `FromNat` (nat → limbs). **Verified (5).**
- `src/BigInt.dfy` — signed sign+magnitude wrapper: `Add` `Sub` `Mul` `Compare`
  `Negate` `Abs` vs `IntValue()`. **Verified (11).**
- `src/Rational.dfy` — `num`/`den` over `BigInt`, kept in lowest terms via gcd.

## Z3 instability note (important for anyone extending this)

Nonlinear products of recursive functions (`Value(q)*Value(ys)`, `IntValue`,
etc.) make Z3 unstable here: a lemma can time out just setting up a context
whose precondition contains such a product, independent of its body. The fix
used throughout: keep `Value()`/`IntValue()` out of any nonlinear context — bind
them to plain `nat`/`int` locals up front, form each product once as an opaque
local, and push all multiplication algebra into pure nat/int helper lemmas
(`FoldArithSub`, `HalfRecArith`, `ParityCombineNat`, `MulSignValue`, the gcd
`Divides*` lemmas). `@IsolateAssertions` helps only once the recursion is gone
from the context. Module-wide `@DisableNonlinearArithmetic` was tried and made
it worse (broke the small multiplication lemmas), so it is not used.

## Scope: minimal, not fast

Explicitly **no performance work**. No Karatsuba/Toom multiplication, no
Newton/Knuth-D division, no limb-level micro-optimisation. Only the minimum an
arbitrary-precision int + rational needs: schoolbook add/sub/mul, plain long
division, Euclidean gcd, gcd-reduced rationals. Simple and verifiable beats
fast. Speed is a possible phase-2 concern, deliberately out of scope here.

## Word width in the proof vs. in generated C++

A note, because it is easy to conflate the two:

- **In the Dafny proof model** limbs are nat-backed and arithmetic runs in
  unbounded `nat`. `x + y + carry` and `x*m + carry` are just nats; the carry is
  `s / BASE`, the digit is `s % BASE`. There is no fixed-width container, so no
  overflow question — the width (`< 2^32`) is only the digit invariant, not the
  type things are computed in.
- **In generated native C++ (phase 2)** the fixed-width argument returns: with
  32-bit limbs, an addition needs a 64-bit intermediate (two 32-bit values plus
  carry is up to 33 bits) and a multiplication needs 64 bits (32×32 → up to 64);
  64-bit limbs would need 128-bit intermediates. That belongs in the codegen /
  runtime layer, not in the verified nat model. 32-bit limbs were chosen partly
  so the native mul intermediate is a plain `uint64`, not `__uint128`.

## Verification contract

Every operation carries a postcondition stated in terms of `Value()` (or, for
signed, the mathematical integer it denotes). No `assume`, no `{:axiom}`, no
proof-suppressing `assert`. `scripts/verify.sh` verifies the whole `src/` tree.

## Open items / TODO

- DivMod full proof (long division quotient estimation) — the known hard part.
- Phase-2 runtime integration is out of scope here.

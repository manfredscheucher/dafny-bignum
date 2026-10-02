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

> **Correction (later finding):** the original note here said "rationals need
> gcd to keep representatives small". That is wrong for the actual target use —
> Dafny's `real`. See the "Rational is parked" section below. The integer layer
> (`BigInt`) is what the C++ backend's `DafnyReal` actually needs.

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

## Rational is parked — and why (read before touching Rational.dfy)

`src/Rational.dfy` reduces every result to lowest terms via gcd (`Make` is
coprime-by-construction). That is correct for a *mathematical* rational, but it
is the **wrong semantics for Dafny's `real`**, which is the only reason a
rational layer was wanted here.

Dafny's `real` is an *unreduced* num/den pair, on purpose: the denominator
carries how many decimal places `print` shows. `1.5 * 1.0` is 150/100 and prints
`1.50`; reducing it to 3/2 would print `1.5` and break byte-compatibility with
the C#/Java/Python backends. The real C++ backend (`--bignum=boost`) therefore
uses `DafnyReal` = two `DafnyBigInt` kept **unreduced** (mirroring C#'s
`Dafny.BigRational`), and only `DafnyBigInt` is backed by Boost `cpp_int`. It
deliberately does **not** use `cpp_rational`, precisely because that auto-reduces.

Consequences:
- The auto-reducing `Rational` here does not model `DafnyReal`. It is **parked**
  as-is (verified, but not the thing the backend needs). Not deleted — it is a
  correct mathematical rational and may be useful elsewhere.
- A faithful `DafnyReal` would be an unreduced `(num: BigInt, den: BigInt)` pair
  with **no** automatic gcd. If/when that is built, reduction must be an explicit
  opt-in operation, never automatic.
- `GCD`/`GCDFast` are therefore **not** needed for the `real` use case. Kept as
  optional verified building blocks (they do no harm, usable for an explicit
  `Reduce()` or elsewhere) — but nothing should call them automatically.
- **The integer layer (`BigInt`) is the real deliverable** for the C++ backend:
  it is what `DafnyBigInt` / unbounded `int` maps to, and what `DafnyReal` is
  built out of. Focus is there, not on the rational layer.

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
- `src/BigNatGCD.dfy` — Euclidean gcd (`gcd(a,b)=gcd(b, a mod b)`), proved
  against a mathematical `IsGCD` predicate. **Verified (16).**
- `src/BigNatConv.dfy` — `FromNat` (nat → limbs). **Verified (5).**
- `src/BigInt.dfy` — signed sign+magnitude wrapper: `Add` `Sub` `Mul` `Compare`
  `Negate` `Abs` vs `IntValue()`. **Verified (11).**
- `src/PureArith.dfy` — pure nat/int/real helper lemmas, deliberately with no
  BigNat import so the recursive `Value` axioms stay out of their context (see
  the Z3 note below). **Verified (25).**
- `src/Rational.dfy` — `num`/`den` over `BigInt`, kept in lowest terms via gcd.
  `Add` `Sub` `Mul` `Compare` vs `RatValue()` (a `real`). `Make` is `opaque` so
  its gcd reduction does not unfold into callers' Z3 context. **Verified (138).**

The whole tree (`scripts/verify.sh`) verifies with 0 errors and no `assume`,
`{:axiom}` or `{:verify false}`. Regression tests under `test/` (themselves
verified lemmas) check concrete results for each layer; `examples/demo.dfy` runs.

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

**Phase 2 is where the boost dilemma is actually settled — and it is not done.**
Phase 1 (this repo) is a standalone, fully verified library. But every operation
is specified against `Value(): nat` and computes its carries in Dafny's
unbounded `nat`/`int`. In generated C++, Dafny `nat`/`int` *is* `DafnyInt` =
Boost `cpp_int`. So a naive translation of this library would pull Boost back in
for its own intermediate values. Replacing Boost needs the fixed-width rewrite
(carries in `uint64`, sequence lengths/indices on bounded types rather than the
runtime big int) — and the Phase-1 proofs do **not** carry over automatically,
because that step replaces the computation model. Recommended next move: a small
spike on ONE operation (e.g. `AddCarry` specified against `uint64` bounds) to
check whether its C++ output is Boost-free, before building further. Until that
spike, "verified in Dafny → translate → Boost gone" is an assumption, not a
result. (Flagged by an independent concept review.)

- **GCD algorithm:** `BigNatGCD` uses textbook Euclid (`gcd(a,b)=gcd(b,a mod b)`),
  worst case Fibonacci-many steps — not the `min(p%q, q-(p%q))` variant. Purely a
  performance choice (repo scope is "no perf work"); correctness of reduction is
  unaffected. Open for Manfred to decide if the variant is wanted.
- **Performance unmeasured:** DivMod is recursive binary long division
  (quadratic in bit length). Fine for a verified lib; as a Boost *replacement* a
  micro-benchmark against a realistic baseline is still owed before calling it
  "simple beats fast".
- **Duplicated lemmas:** small multiplication/commutativity lemmas (`MulComm`,
  `MulAssoc`, distributivity) still appear in several modules; `PureArith.dfy`
  now exists as the home to consolidate them into. Mechanical cleanup, not yet
  done (touching verified files risks destabilising proofs — do it carefully).
- **`Value` is a non-ghost function** used in demos' `print`. Marking it `ghost`
  (with a separate executable `ToNat` for demos) would make the math-vs-runtime
  boundary explicit. Minor.

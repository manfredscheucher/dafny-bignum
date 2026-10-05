# dafny-bignum — TODO / backlog

Open items, ordered roughly by value. Nothing here is required for the current
library to be correct; it is all either performance, polish, or the (large)
phase-2 question. Each item records enough context to pick it up cold.

## Big open question (not scheduled)

### Phase 2: actually replace Boost in the C++ backend
The whole motivation was removing the external big-integer dependency from
Dafny's C++ runtime. But Phase 1 (this repo) proves everything against
`Value(): nat` and computes intermediates in Dafny's unbounded `nat`/`int` —
which *is* `DafnyInt` / Boost `cpp_int` in generated C++. So "verify + translate"
does **not** by itself remove Boost.

The real work: re-express the limb arithmetic so intermediates provably fit in
fixed-width machine words (`uint64` for 32-bit limbs), spec against bounded
types instead of `nat`, and make sequence lengths/indices bv-based. Phase-1
proofs do **not** carry over directly, because the computation model changes.

Recommended first step: a spike on ONE operation (e.g. `AddCarry`) re-specified
against `uint64` bounds, then inspect the generated C++ — is it Boost-free? That
answers the viability of the entire project while the library is still small.

### Why this is worth it — the real maintainer argument
Checked across Dafny's runtimes (see `dafny/_private/cpp/NOTES_bignum_real_across_targets.md`):
`real` is a hand-written num/den `BigRational` in **four** backends (C#, Java,
JS, C++) — not shared code, the same gcd-normalize/IsPowerOf10/DividesAPowerOf10/
ToString logic re-written per language, partly verbatim copy-paste (an identical
comment appears in C# `DafnyRuntime.cs:2093` and Java `BigRational.java:159`).
Plus external int deps: JS `bignumber.js`, Rust `num`, C++ Boost. A bignum
proved in Dafny only needs `int`; `real` falls out as the num/den pair on top
(this repo's `DafnyReal`). So `--bignum=dafny` would replace four duplicated
hand-written BigRationals **and** three external int libraries with one verified,
target-independent implementation. That is the case for it being "the way to
go", not a nicety. (Belongs in the upstream issue, phrased human/short.)

## Performance (all optional; measure before committing to any)

### DivMod: bit-wise → limb-wise (~32× constant factor)  — recommended: leave
Current `DivMod` does schoolbook **bit-by-bit** long division: ~32·n iterations
for n limbs (one compare + maybe one subtract over the full width per bit).
Limb-wise long division (base 2^32) would do **n** iterations instead — roughly
32× fewer. BUT: each limb-step must *guess* a 32-bit quotient digit and correct
it (this is Knuth's Algorithm D). The guess-is-off-by-≤2 lemma and the
correction-converges proof are hard, over exactly the nonlinear `Value()`
arithmetic that already destabilises Z3 here. So: ~32× faster, proof effort goes
from "moderate (done)" to "hardest thing in the repo". It is only a constant
factor (division stays quadratic in width), and it only matters at all once the
lib runs as native C++ (phase 2) — in Dafny-`nat` it is not the bottleneck.
If ever done: add a separate `DivModFast` beside the simple proven `DivMod`
(like GCD / GCDFast), keeping the simple one as the reference. Trigger: only if
a real measurement shows division is the bottleneck.

### base 2^32 → 2^64 limbs (~2× fewer limbs)  — grenzwertig
Halving the limb count roughly halves the work of every O(n)/O(n^2) operation.
With nat-backed limbs the old bv-cast problem does not recur, but every "product
fits" argument (mul, divmod) must be redone for 2^64 limbs where a single-limb
product no longer fits a machine word in the eventual C++ (needs `__uint128`).
Moderate-to-heavy proof rework. Defer until phase-2 direction is decided.

### Rational: cheaper reduction in easy cases  — small win
`Make` runs a full gcd after every op. Cheap shortcuts already added: zero
numerator → 0/1 with no gcd. Possible further ones: equal denominators (add
numerators, keep denominator, gcd only once); one denominator divides the other.
Low risk (Make is opaque), small but real. Not yet done.

## Correctness / robustness

### BigNatGCD: a proof sits near the time limit  — should fix
`scripts/verify.sh` occasionally reports 1 time out in `BigNatGCD.dfy` at a 55s
limit (passes at 45s). Z3 variance, but it means one GCD proof is too close to
the edge. Tighten it (bind values to nats earlier / split the lemma) so it
verifies comfortably and deterministically. Same pattern used elsewhere.

### test/nat_limb_feasibility.dfy  — DONE
Was a deliberately-failing doc probe; now proved (`MulFits` closed) and moved to
`doc/experiments/`. `verify.sh` is green again. Kept here for history.

### DafnyReal.ToString  — mostly done; one formal step left
`src/DafnyReal.dfy` models Dafny's `BigRational`, verified for all arithmetic
(Normalize/Add/Sub/Neg/Mul/Div/Compare vs `RealValue`) and the decimal-print
path: `DecimalString(n)` is now proved correct against `DenotesDecimal` (only
digits, no leading zero, `ParseDec(s)==n`), and `ToString` assembles the three
C# cases (`"num.0"`, decimal via `factor`/`log10` with `factor*den==10^log10`,
`"(num.0 / den.0)"`) on those verified pieces.
REMAINING: `ToString` carries no parse-back `ensures` — proving that the
assembled string, parsed as a decimal fraction, equals `RealValue(x)` needs a
`DenotesDecimalFraction(s, num, den)` relation the library does not define. That
is the single last step for provably-correct `real` printing. No false spec is
claimed meanwhile.

## Polish

- Lemma duplication across modules (`MulComm`/`MulAssoc`/`Distrib*` defined in
  several files). `PureArith.dfy` now exists as the shared home — migrate the
  duplicates there and import.
- `doc/SPEC.md` module map / verified-lemma counts drift as files change; refresh
  from a clean `verify.sh` run when touching the docs.

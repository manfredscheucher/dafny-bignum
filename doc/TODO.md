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

### test/nat_limb_feasibility.dfy is a doc probe, not a passing test
It deliberately contains an unproved obligation (the bv-vs-nat feasibility
experiment that motivated nat-backed limbs). It must NOT be in the set
`verify.sh` treats as "must pass" — it currently makes the script report
VERIFICATION FAILED. Either move it out of `test/` (e.g. to `doc/experiments/`)
or mark it clearly as expected-to-fail. See also `doc/bv-model-abandoned.dfy.txt`.

## Polish

- Lemma duplication across modules (`MulComm`/`MulAssoc`/`Distrib*` defined in
  several files). `PureArith.dfy` now exists as the shared home — migrate the
  duplicates there and import.
- `doc/SPEC.md` module map / verified-lemma counts drift as files change; refresh
  from a clean `verify.sh` run when touching the docs.

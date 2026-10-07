# Fixed-width BigNat — the Boost-free rebuild

The `src/` library is fully verified but computes carries in Dafny `int`, which
every backend emits as its big-integer type (C++ `BigNumber`=Boost cpp_int, JS
bignumber.js, Rust num). So `src/` does NOT replace those libraries — it uses
them. This `fw/` rebuild fixes that.

## The rule

Every EXECUTABLE value is a fixed-width `newtype` with a NativeType:
- `limb`  = `newtype x: int | 0 <= x < 2^32`  -> native `uint32`
- `dword` = `newtype x: int | 0 <= x < 2^64`  -> native `uint64`

`int`/`nat` appear ONLY in ghost specs (`Value`, lemmas), never in compiled
code. That is what keeps the generated code native.

## Two gates per operation (both must pass before moving on)

1. `Dafny verify` — green.
2. `Dafny translate cpp --no-verify --unicode-char:false <f>.dfy` must itself
   produce NO errors (an "Unbounded integers" / "Non-native numeric newtypes"
   error means a stray int/nat in compiled code), AND the generated .cpp/.h must
   contain no `BigNumber|boost|cpp_int`. Checking only the grep is NOT enough —
   a failed translate emits no file, so the grep falsely "passes".

## Status — the full fixed-width stack, every module through both gates

- `FwNat.dfy`: `limb`/`dword`, ghost `Value`, `AddColumn`, `AddSeq`. Verified, Boost-free.
- `FwSub.dfy`: `SubColumn`, `SubSeq` (borrow-threaded). Verified, Boost-free.
- `FwMul.dfy`: `MulAddColumn`, `MulLimb`, `ShiftOne`, `AddFull`, schoolbook `Mul`. Verified, Boost-free.
- `FwCompare.dfy`: `cmp` newtype result, LSB-recursive `Compare`. Verified, Boost-free.
- `FwDivMod.dfy`: recursive binary long division, `Normalize`, `SplitLast`. Verified, Boost-free.
- `FwInt.dfy`: signed sign+magnitude `Add/Sub/Mul/Compare/Negate/Abs`. Verified, Boost-free.
- `FwReal.dfy` (+ `FwRealArith.dfy`): unreduced num/den `Add/Sub/Mul/Div/Compare`
  vs `RealValue` (Dafny `BigRational` semantics). Verified, Boost-free.

Optional / not done: decimal `ToString` for FwReal, gcd reduction (not needed
for the unreduced `real` semantics). The `src/` library (nat-limb, fully
verified incl. ToString parse-back) stays as the maths reference.

## Gotcha: no `nat`/`int` counters in compiled code

`int`/`nat` in ghost specs is fine. But a free `nat`/`int` used as a COMPILED
value — a method parameter like `Shift(k: nat)` / `PadTo(n: nat)`, or a local
counter — makes Dafny emit "Unbounded integers" (BigNumber/Boost) and fails
Gate 2. Sequence lengths via `|s|` are fine (compile to `size_t`). Rule: recurse
on the sequences themselves, never pass a numeric `nat`/`int` count into a
compiled method. (Cost two rewrites in `FwMul`.)

More instances of the same family (all fixed the same way — keep int/nat ghost
or use a native type):
- A comparison method returning `int` → use a `newtype cmp = x: int | -1<=x<=1`
  (native). Negating a `cmp` via `(0 - c as int) as cmp` reintroduces the int —
  do it with a `if c<0/>0/else` case split instead. (`FwCompare`, `FwInt`.)
- A most-significant element access `xs[|xs|-1]` compiles the `|xs|-1` as a
  non-native int. Use LSB recursion, or a `SplitLast` helper, or make the index
  a `ghost var` if it is only used by proof lemmas. (`FwDivMod`.)
- A transient `as int` inside any compiled expression is enough to pull in
  unbounded integers. (`FwInt`, `FwReal`.)

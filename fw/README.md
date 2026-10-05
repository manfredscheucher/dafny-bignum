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
2. `Dafny translate cpp --no-verify --unicode-char:false <f>.dfy` then
   `grep -iE 'BigNumber|boost|cpp_int'` the generated .cpp/.h — must be EMPTY.

## Status

- `FwNat.dfy`: `limb`/`dword`, ghost `Value`, `AddColumn`, `AddSeq`. Verified
  (13/0), Boost-free.
- `FwSub.dfy`: `SubColumn`, `SubSeq` (borrow-threaded). Verified (7/0), Boost-free.
- `FwMul.dfy`: `MulAddColumn`, `MulLimb`, `ShiftOne`, `AddFull`, schoolbook `Mul`.
  Verified (31/0), Boost-free.
- Next: DivMod, signed int, real.

## Gotcha: no `nat`/`int` counters in compiled code

`int`/`nat` in ghost specs is fine. But a free `nat`/`int` used as a COMPILED
value — a method parameter like `Shift(k: nat)` / `PadTo(n: nat)`, or a local
counter — makes Dafny emit "Unbounded integers" (BigNumber/Boost) and fails
Gate 2. Sequence lengths via `|s|` are fine (compile to `size_t`). Rule: recurse
on the sequences themselves, never pass a numeric `nat`/`int` count into a
compiled method. (Cost two rewrites in `FwMul`.)

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
  (13/0). Generated C++ is Boost-free (`AddSeq` is `DafnySequence<uint32>` +
  uint32/uint64 arithmetic, no BigNumber). Next: Sub, Mul, DivMod, sign, real.

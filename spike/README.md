# Fixed-width spike — can we drop Boost?

Question: the verified library computes carries in Dafny `int`, which the C++
backend emits as `BigNumber` (= Boost `cpp_int`). Can one operation instead be
written so the generated C++ uses only native `uint32`/`uint64`, no Boost?

`AddCarrySpike.dfy`: `AddLimb` with `newtype limb (< 2^32)` and a `uint64`-ranged
intermediate. Verifies in Dafny (5/0), and:

    Dafny translate cpp --no-verify --unicode-char:false AddCarrySpike.dfy

generates `AddLimb(uint32, uint32, uint32) -> Tuple<uint32,uint32>` with a
`uint64` intermediate and **no BigNumber / Boost / cpp_int anywhere** in the
output. `grep -i 'BigNumber|boost|cpp_int'` on the generated .cpp/.h: nothing.

Conclusion: NativeType-annotated `newtype` limbs make the generated code
Boost-free (and, being native types, the same holds for every target). So
replacing the external bignum libraries with this verified library is viable —
but it requires the whole library's limbs/intermediates to move from `nat` to
these fixed-width newtypes. This spike proves one operation; the rest is work.

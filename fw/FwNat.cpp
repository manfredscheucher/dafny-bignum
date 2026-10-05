// Dafny program FwNat.dfy compiled into Cpp
#include "DafnyRuntime.h"
using namespace std::literals;
#include "FwNat.h"
namespace FwNat  {

  struct Tuple<uint32, uint32> __default::AddColumn(uint32 a, uint32 b, uint32 cin)
  {
    uint32 lo = 0;
    uint32 cout = 0;
    uint64 _0_s;
    _0_s = ((uint64(a)) + (uint64(b))) + (uint64(cin));
    lo = uint32((_0_s) % (FwNat::__default::BASE));
    cout = uint32((_0_s) / (FwNat::__default::BASE));
    return Tuple<uint32, uint32>(lo, cout);
  }
  struct Tuple<DafnySequence<uint32>, uint32> __default::AddSeq(DafnySequence<uint32> xs, DafnySequence<uint32> ys, uint32 cin)
  {
    DafnySequence<uint32> zs = DafnySequence<uint32>();
    uint32 cout = 0;
    if (((xs).size()) == (0)) {
      DafnySequence<uint32> _rhs0 = DafnySequence<uint32>::Create({});
      uint32 _rhs1 = cin;
      zs = _rhs0;
      cout = _rhs1;
      return Tuple<DafnySequence<uint32>, uint32>(zs, cout);
    }
    uint32 _0_lo;
    uint32 _1_c1;
    uint32 _out0;
    uint32 _out1;
    auto _outcollector0 = FwNat::__default::AddColumn((xs).select(0), (ys).select(0), cin);
    _out0 = _outcollector0.template get<0>();
    _out1 = _outcollector0.template get<1>();
    _0_lo = _out0;
    _1_c1 = _out1;
    DafnySequence<uint32> _2_rest;
    uint32 _3_c2;
    DafnySequence<uint32> _out2;
    uint32 _out3;
    auto _outcollector1 = FwNat::__default::AddSeq((xs).drop(1), (ys).drop(1), _1_c1);
    _out2 = _outcollector1.template get<0>();
    _out3 = _outcollector1.template get<1>();
    _2_rest = _out2;
    _3_c2 = _out3;
    zs = (DafnySequence<uint32>::Create({_0_lo})).concatenate(_2_rest);
    cout = _3_c2;
    return Tuple<DafnySequence<uint32>, uint32>(zs, cout);
  }
   uint64 __default::BASE =  init__BASE();

  typedef uint32 limb;

  typedef uint64 dword;
}// end of namespace FwNat 
namespace _module  {

}// end of namespace _module 
template <>
struct get_default<std::shared_ptr<FwNat::__default > > {
static std::shared_ptr<FwNat::__default > call() {
return std::shared_ptr<FwNat::__default >();}
};
template <>
struct get_default<std::shared_ptr<FwNat::class_limb > > {
static std::shared_ptr<FwNat::class_limb > call() {
return std::shared_ptr<FwNat::class_limb >();}
};
template <>
struct get_default<std::shared_ptr<FwNat::class_dword > > {
static std::shared_ptr<FwNat::class_dword > call() {
return std::shared_ptr<FwNat::class_dword >();}
};

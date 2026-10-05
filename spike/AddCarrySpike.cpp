// Dafny program AddCarrySpike.dfy compiled into Cpp
#include "DafnyRuntime.h"
using namespace std::literals;
#include "AddCarrySpike.h"
namespace _module  {

  struct Tuple<uint32, uint32> __default::AddLimb(uint32 a, uint32 b, uint32 cin)
  {
    uint32 lo = 0;
    uint32 cout = 0;
    uint64 _0_s;
    _0_s = ((uint64(a)) + (uint64(b))) + (uint64(cin));
    lo = uint32((_0_s) % (_module::__default::BASE));
    cout = uint32((_0_s) / (_module::__default::BASE));
    return Tuple<uint32, uint32>(lo, cout);
  }
   uint64 __default::BASE =  init__BASE();

  typedef uint32 limb;

  typedef uint64 u64;
}// end of namespace _module 
template <>
struct get_default<std::shared_ptr<_module::__default > > {
static std::shared_ptr<_module::__default > call() {
return std::shared_ptr<_module::__default >();}
};
template <>
struct get_default<std::shared_ptr<_module::class_limb > > {
static std::shared_ptr<_module::class_limb > call() {
return std::shared_ptr<_module::class_limb >();}
};
template <>
struct get_default<std::shared_ptr<_module::class_u64 > > {
static std::shared_ptr<_module::class_u64 > call() {
return std::shared_ptr<_module::class_u64 >();}
};

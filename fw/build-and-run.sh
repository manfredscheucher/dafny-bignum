#!/usr/bin/env bash
# End-to-end proof that the fixed-width stack generates Boost-free C++ that
# actually compiles and runs. Translates fw/FwTest.dfy to C++, builds it with a
# plain g++ (NO -DDAFNY_BIGNUM_BOOST, NO Boost include path — only the Dafny C++
# runtime header), and runs it. The runtime checks inside Main use `expect`, so
# a wrong result aborts with a nonzero exit.
#
# Usage:  fw/build-and-run.sh
# Requires: the self-built Dafny with the C++ backend, and g++ (C++17).
set -euo pipefail

FW="$(cd "$(dirname "$0")" && pwd)"
DAFNY="${DAFNY:-$HOME/github/dafny/Binaries/Dafny}"
RUNTIME="${DAFNY_CPP_RUNTIME:-$HOME/github/dafny/Binaries/DafnyRuntimeCpp}"

cd "$FW"
rm -f FwTest.cpp FwTest.h FwTest_exe

echo "== translate FwTest.dfy -> C++ (no verify) =="
"$DAFNY" translate cpp --no-verify --unicode-char:false FwTest.dfy >/dev/null

echo "== assert the generated C++ pulls in NO big-integer library =="
if grep -qiE 'BigNumber|boost|cpp_int|gmp|mpz' FwTest.cpp FwTest.h; then
  echo "FAIL: generated C++ references a big-integer library" >&2
  grep -niE 'BigNumber|boost|cpp_int|gmp|mpz' FwTest.cpp FwTest.h >&2
  exit 1
fi
echo "   ok: no BigNumber/boost/cpp_int/gmp in the generated code"

echo "== g++ build (plain, no Boost flag, no Boost -I) =="
g++ -std=c++17 -I "$RUNTIME" -o FwTest_exe FwTest.cpp

echo "== run =="
./FwTest_exe

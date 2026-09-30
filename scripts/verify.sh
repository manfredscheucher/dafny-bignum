#!/usr/bin/env bash
# Verify the whole dafny-bignum source tree.
# Each file is checked with a short per-file time limit so a hung proof fails
# fast instead of blocking. Run from anywhere.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

TIME_LIMIT="${DAFNY_TIME_LIMIT:-60}"   # seconds per verification, override via env
FILES=(src/*.dfy)

fail=0
for f in "${FILES[@]}"; do
  [ -e "$f" ] || continue
  printf '=== verify %s ===\n' "$f"
  if ! dafny verify --verification-time-limit "$TIME_LIMIT" "$f"; then
    fail=1
  fi
done

if [ "$fail" -ne 0 ]; then
  echo "VERIFICATION FAILED" >&2
  exit 1
fi
echo "all verified"

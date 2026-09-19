#!/usr/bin/env bash
# The gate: every test green before every commit.
#   ./gate.sh
set -u
cd "$(dirname "$0")"
fail=0
for t in tests/*.sh; do
  echo "--- $t"
  "$t" || fail=1
done
[ $fail = 0 ] && echo "GATE: green" || echo "GATE: red"
exit $fail

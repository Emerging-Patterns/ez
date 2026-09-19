#!/usr/bin/env bash
# The gate: green before every commit.
#   ./gate.sh            every lane
#   ./gate.sh --js-only  skip the native lane, which builds a binary per test
set -u
cd "$(dirname "$0")"
js_only=0; [ "${1:-}" = "--js-only" ] && js_only=1
pass=0; total=0
check() { # name, expected, observed
  total=$((total + 1))
  if [ "$2" = "$3" ]; then
    pass=$((pass + 1))
  else
    echo "FAIL: $1"; diff <(echo "$2") <(echo "$3") | sed 's/^/  /'
  fi
}
# bend reports its unsafe annotations on stderr after the check; that is not the
# program's output, and a test's `#|` lines do not carry it
run() { local out; out=$("$@" 2>&1); local st=$?; printf '%s\n' "$out" | grep -v '^All terms check, with [0-9]* unsafe annotation'; return $st; }

# every .bend test must print the `#|` lines in its trailer, on each lane
for t in */tests/*.bend; do
  [ -f "$t" ] || continue
  want=$(sed -n 's/^#|//p' "$t")
  check "$t (js)" "$want" "$(run bend "$t")"
  [ $js_only = 1 ] && continue
  bin=".gate/$(basename "$t" .bend)"
  mkdir -p .gate
  if ! built=$(run bend "$t" -o "$bin"); then
    check "$t (build)" "" "$built"; continue
  fi
  check "$t (cpu)" "$want" "$("$bin" --gpu off 2>&1)"
done

# the shell tests drive the tools end to end
for t in tests/*.sh; do
  check "$t" "" "$("$t" >/dev/null 2>&1; [ $? = 0 ] || echo failed)"
done

echo "PASS: $pass / $total"
[ "$pass" = "$total" ]

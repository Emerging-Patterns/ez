#!/usr/bin/env bash
# Pins the package hash against bend itself: `bend --publish` runs at a local
# hub, and the hash it mines must equal the one ez computes without publishing.
# If bend's packaging ever changes, this fails instead of the hashes silently
# diverging.
#
# The fixture is tests/fixture, the layout that makes a package interesting: a
# nested module, a foreign body beside that module, and a module above the
# entry's own directory, which re-roots the package. pkg/tests/walk.bend
# asserts the same hash without paying for the proof of work.
#   ./tests/publish.sh
set -u
cd "$(dirname "$0")/.."
export BEND_LIB="${BEND_LIB:-$PWD/.ez/lib}"
root=$(mktemp -d)
trap 'st=$?; kill %1 2>/dev/null; rm -rf "$root"; exit $st' EXIT
pass=0; total=0
check() { # name, expected, observed
  total=$((total + 1))
  if [ "$2" = "$3" ]; then pass=$((pass + 1)); else
    echo "FAIL: $1"; diff <(echo "$2") <(echo "$3") | sed 's/^/  /'
  fi
}

mkdir -p "$root/hub"
port=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()')
bun tests/oracle.ts "$root/hub" "$port" &
for _ in $(seq 50); do curl -fsS "http://127.0.0.1:$port/" >/dev/null 2>&1 && break; sleep 0.1; done

# the proof of work takes tens of seconds; it is the price of asking bend itself
got=$(cd tests/fixture && BEND_HUB=http://127.0.0.1:$port bend src/lib.bend --publish 2>/dev/null | head -1)
mine=$(EZ_ENTRY=tests/fixture/src/lib.bend bend pkg/main.bend 2>/dev/null)

check "ez computes the hash bend publishes" "$got" "$(printf '%s\n' "$mine" | sed -n 1p)"
check "ez names the directory the package is rooted at" "tests/fixture" \
  "$(printf '%s\n' "$mine" | sed -n 2p)"
check "ez computes the manifest bend publishes" \
  "$(cat "$root/hub/$got/manifest")" \
  "$(printf '%s\n' "$mine" | tail -n +3)"

# bin/ez-git.ts still computes the package in TypeScript; it must agree with
# the Bend that replaced it, until it too is ported and bin/pkg.ts goes
check "bin/pkg.ts agrees with pkg/" "$got" \
  "$(bun -e 'import {pkg_of} from "./bin/pkg.ts"; console.log(pkg_of(process.argv[1]).hash)' tests/fixture/src/lib.bend)"

echo "PASS: $pass / $total"
[ "$pass" = "$total" ]

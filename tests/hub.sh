#!/usr/bin/env bash
# Builds a two-level fake hub (package B imports package A), locks an entry
# against it, then proves the locked BEND_LIB builds with the hub unreachable.
#   ./tests/hub.sh
set -u
# the gate exports BEND_LIB for its own lanes; a test picks its own
unset BEND_LIB
cd "$(dirname "$0")/.."
root=$(mktemp -d)
trap 'st=$?; kill %1 2>/dev/null; rm -rf "$root"; exit $st' EXIT
pass=0; total=0
check() { # name, expected, observed
  total=$((total + 1))
  if [ "$2" = "$3" ]; then pass=$((pass + 1)); else
    echo "FAIL: $1"; diff <(echo "$2") <(echo "$3") | sed 's/^/  /'
  fi
}

# a hub package is a directory named by its hash, holding `manifest` (one
# `<sha256> <path>` line per file) and the files. The hash is sha256 over that
# manifest text, cut to 32 hex characters, the way `bend --publish` computes it.
publish() { # dir -> prints the hash
  local dir=$1 man="" h sum at
  for at in $(cd "$dir" && find . -name '*.bend' | sed 's|^\./||' | sort); do
    sum=$(sha256sum "$dir/$at" | cut -d' ' -f1)
    man="$man$sum $at"$'\n'
  done
  h="0x$(printf '%s' "$man" | sha256sum | cut -c1-32)"
  for at in $(cd "$dir" && find . -name '*.bend' | sed 's|^\./||' | sort); do
    mkdir -p "$root/hub/$h/$(dirname "$at")"
    cp "$dir/$at" "$root/hub/$h/$at"
  done
  printf '%s' "$man" > "$root/hub/$h/manifest"
  echo "$h"
}

mkdir -p "$root/a/src" "$root/b/src" "$root/app" "$root/empty"
cat > "$root/a/src/lib.bend" <<'EOF'
import Base

# double the number
def double(+x: U32) -> U32:
  (x * 2 : U32)
EOF
A=$(publish "$root/a")

cat > "$root/b/src/mid.bend" <<EOF
import Base
import $A/src/lib.bend as A

# four times the number
def quad(+x: U32) -> U32:
  A.double(A.double(x))
EOF
B=$(publish "$root/b")

cat > "$root/app/main.bend" <<EOF
import Base
import $B/src/mid.bend as B

def main() -> U32:
  B.quad(11)
EOF

# a port of our own, so a stray server elsewhere cannot answer for the hub
port=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()')
(cd "$root/hub" && python3 -m http.server "$port" --bind 127.0.0.1 >/dev/null 2>&1) &
for _ in $(seq 50); do curl -fsS "http://127.0.0.1:$port/" >/dev/null 2>&1 && break; sleep 0.1; done

export BEND_HUB=http://127.0.0.1:$port
bun bin/ez-lock.ts "$root/app/main.bend" > "$root/ez.lock.json"

check "the lock names both packages, the direct one and its own dependency" \
  "$A
$B" \
  "$(python3 -c 'import json,sys; print("\n".join(sorted(json.load(open(sys.argv[1]))["packages"])))' "$root/ez.lock.json")"

# populate BEND_LIB from the lock alone, the way the nix derivation does
lib="$root/lib"
python3 - "$root/ez.lock.json" "$lib" "$root/hub" <<'PY'
import json, os, shutil, sys
lock, lib, hub = json.load(open(sys.argv[1])), sys.argv[2], sys.argv[3]
for h, entry in lock["packages"].items():
    for at in entry["files"]:
        dst = os.path.join(lib, h, at)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copyfile(os.path.join(hub, h, at), dst)
PY

kill %1 2>/dev/null || true
export BEND_HUB=http://127.0.0.1:1   # the hub is gone

check "the locked lib builds with the hub unreachable" "44" \
  "$(cd "$root/app" && BEND_LIB=$lib bend main.bend 2>&1 | tail -1)"

check "without the locked lib the same build fails" "1" \
  "$(cd "$root/app" && BEND_LIB=$root/empty bend main.bend >/dev/null 2>&1; echo $?)"

echo "PASS: $pass / $total"
[ "$pass" = "$total" ]

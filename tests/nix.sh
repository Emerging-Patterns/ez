#!/usr/bin/env bash
# Proves the nix path: lock a project against a local hub, then build it with
# `nix-build`, where the sandbox reaches the hub only through the lock's
# fixed-output fetches.
#   ./tests/nix.sh
set -u
# the gate exports BEND_LIB for its own lanes; a test picks its own
unset BEND_LIB
cd "$(dirname "$0")/.."
root=$(mktemp -d)
trap 'st=$?; kill %1 2>/dev/null; rm -rf "$root"; exit $st' EXIT

mkdir -p "$root/a/src" "$root/app"
cat > "$root/a/src/lib.bend" <<'EOF'
import Base

# double the number
def double(+x: U32) -> U32:
  (x * 2 : U32)
EOF

man=$(sha256sum "$root/a/src/lib.bend" | cut -d' ' -f1)" src/lib.bend"
A="0x$(printf '%s\n' "$man" | sha256sum | cut -c1-32)"
mkdir -p "$root/hub/$A/src"
cp "$root/a/src/lib.bend" "$root/hub/$A/src/lib.bend"
printf '%s\n' "$man" > "$root/hub/$A/manifest"

cat > "$root/app/main.bend" <<EOF
import Base
import $A/src/lib.bend as A

def main() -> U32:
  A.double(21)
EOF

port=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()')
(cd "$root/hub" && python3 -m http.server "$port" --bind 127.0.0.1 >/dev/null 2>&1) &
for _ in $(seq 50); do curl -fsS "http://127.0.0.1:$port/" >/dev/null 2>&1 && break; sleep 0.1; done

BEND_HUB=http://127.0.0.1:$port bun bin/ez-lock.ts "$root/app/main.bend" > "$root/ez.lock.json"
cat "$root/ez.lock.json"

cat > "$root/build.nix" <<NIX
let pkgs = import <nixpkgs> { };
in pkgs.callPackage $PWD/nix/bend-lib.nix { } $root/ez.lock.json
NIX

out=$(nix-build --no-out-link "$root/build.nix" 2>"$root/nix.log") || { cat "$root/nix.log"; echo "FAIL: nix-build"; exit 1; }
echo "BEND_LIB store path: $out"
find "$out" -type f

kill %1 2>/dev/null || true
got=$(cd "$root/app" && BEND_HUB=http://127.0.0.1:1 BEND_LIB=$out bend main.bend 2>&1 | tail -1)
if [ "$got" = "42" ]; then echo "PASS: 1 / 1"; else echo "FAIL: got '$got', want 42"; exit 1; fi

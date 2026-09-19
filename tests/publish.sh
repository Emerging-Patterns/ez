#!/usr/bin/env bash
# Pins bin/pkg.ts against bend itself: `bend --publish` runs at a local hub, and
# the hash it mines must equal the one ez computes without publishing. If bend's
# packaging ever changes, this fails instead of the hashes silently diverging.
#   ./tests/publish.sh
set -u
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

# a nested layout with a foreign body, the shapes that make pkg_files interesting
mkdir -p "$root/repo/src/util" "$root/hub"
cat > "$root/repo/src/util/math.bend" <<'EOF'
import Base

# double the number
def double(+x: U32) -> U32:
  (x * 2 : U32)
EOF
cat > "$root/repo/src/lib.bend" <<'EOF'
import Base
import ./util/math.bend as M

# four times the number
def quad(+x: U32) -> U32:
  M.double(M.double(x))
EOF

port=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()')
bun tests/oracle.ts "$root/hub" "$port" &
for _ in $(seq 50); do curl -fsS "http://127.0.0.1:$port/" >/dev/null 2>&1 && break; sleep 0.1; done

# the proof of work takes tens of seconds; it is the price of asking bend itself
got=$(cd "$root/repo" && BEND_HUB=http://127.0.0.1:$port bend src/lib.bend --publish 2>/dev/null | head -1)
want=$(bun -e 'import {pkg_of} from "./bin/pkg.ts"; console.log(pkg_of(process.argv[1]).hash)' "$root/repo/src/lib.bend")

check "ez computes the hash bend publishes" "$got" "$want"
check "ez computes the manifest bend publishes" \
  "$(cat "$root/hub/$got/manifest")" \
  "$(bun -e 'import {pkg_of, manifest_of} from "./bin/pkg.ts"; process.stdout.write(manifest_of(pkg_of(process.argv[1]).files))' "$root/repo/src/lib.bend")"

echo "PASS: $pass / $total"
[ "$pass" = "$total" ]

#!/usr/bin/env bash
# Depend on a Bend repo that was never published. ez computes the hash the repo
# would get from `bend --publish`, vendors it under that name, and nix rebuilds
# the same tree from the pinned rev.
#   ./tests/git.sh
set -u
# the gate exports BEND_LIB for its own lanes; a test picks its own
unset BEND_LIB
cd "$(dirname "$0")/.."
ez=$PWD
root=$(mktemp -d)
trap 'st=$?; kill ${daemon:-0} 2>/dev/null; rm -rf "$root"; exit $st' EXIT
pass=0; total=0
check() { # name, expected, observed
  total=$((total + 1))
  if [ "$2" = "$3" ]; then pass=$((pass + 1)); else
    echo "FAIL: $1"; diff <(echo "$2") <(echo "$3") | sed 's/^/  /'
  fi
}

# the upstream repo: never published, only pushed
mkdir -p "$root/upstream/src/util"
cat > "$root/upstream/src/util/math.bend" <<'EOF'
import Base

# double the number
def double(+x: U32) -> U32:
  (x * 2 : U32)
EOF
cat > "$root/upstream/src/lib.bend" <<'EOF'
import Base
import ./util/math.bend as M

# four times the number
def quad(+x: U32) -> U32:
  M.double(M.double(x))
EOF
git -C "$root/upstream" init -q
git -C "$root/upstream" add -A
git -C "$root/upstream" -c user.email=t@t -c user.name=t commit -q -m init
rev=$(git -C "$root/upstream" rev-parse HEAD)

# serve it the way a real remote is served, so the nix sandbox can reach it too
mkdir -p "$root/srv"
git clone -q --bare "$root/upstream" "$root/srv/upstream.git"
git -C "$root/srv/upstream.git" config uploadpack.allowAnySHA1InWant true
git -C "$root/srv/upstream.git" config uploadpack.allowTipSHA1InWant true
port=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()')
git daemon --reuseaddr --listen=127.0.0.1 --port="$port" --base-path="$root/srv" --export-all >/dev/null 2>&1 &
daemon=$!
for _ in $(seq 50); do git ls-remote "git://127.0.0.1:$port/upstream.git" >/dev/null 2>&1 && break; sleep 0.1; done
url="git://127.0.0.1:$port/upstream.git"

# an annotated tag, so the peeled ^{} row is what must be pinned
git -C "$root/upstream" -c user.email=t@t -c user.name=t tag -a v1.0 -m v1.0
git -C "$root/upstream" push -q "$root/srv/upstream.git" v1.0

# our project depends on it
mkdir -p "$root/app"
cd "$root/app"
rec=$(BEND_LIB="$root/app/.ez/lib" bun "$ez/bin/ez-git.ts" "$url" "$rev" src/lib.bend 2>"$root/add.log")
hash=$(echo "$rec" | sed -n 1p)
line=$(grep '^import ' "$root/add.log")

check "the record names the hash, url, rev and entry" \
  "$hash
$url
$rev

src/lib.bend" \
  "$rec"

cat > main.bend <<EOF
import Base
$line

def main() -> U32:
  Lib.quad(11)
EOF

tagged=$(BEND_LIB="$root/app/.ez/tag" bun "$ez/bin/ez-git.ts" "$url" v1.0 src/lib.bend 2>"$root/tag.log" | sed -n 1p)
check "a tag resolves to the same package as its commit" "$hash" "$tagged"
check "the tag it resolved through is written down" "v1.0 is $rev" "$(grep ' is ' "$root/tag.log")"
check "the lock keeps the tag beside the rev" "v1.0" \
  "$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]].get("tag",""))' "$root/app/.ez/origins.json" "$hash")"

check "the vendored package builds, with no hub at all" "44" \
  "$(BEND_HUB=http://127.0.0.1:1 BEND_LIB=$root/app/.ez/lib bend main.bend 2>&1 | tail -1)"

BEND_LIB="$root/app/.ez/lib" bun "$ez/bin/ez-lock.ts" main.bend > ez.lock.json
check "the lock records the git rev, not the hub" "git $rev" \
  "$(python3 -c 'import json,sys; s=json.load(open("ez.lock.json"))["packages"][sys.argv[1]]["source"]; print(s["kind"], s["rev"])' "$hash")"

# nix rebuilds the same tree from the rev alone
cat > build.nix <<NIX
let pkgs = import <nixpkgs> { };
in pkgs.callPackage $ez/nix/bend-lib.nix { } $root/app/ez.lock.json
NIX
out=$(nix-build --no-out-link build.nix 2>"$root/nix.log") || { cat "$root/nix.log"; echo "FAIL: nix-build"; exit 1; }

check "nix rebuilds the package byte for byte" \
  "$(cd "$root/app/.ez/lib/$hash" && find . -type f | sort | xargs sha256sum)" \
  "$(cd "$out/$hash" && find . -type f | sort | xargs sha256sum)"

check "the nix tree builds with no hub" "44" \
  "$(BEND_HUB=http://127.0.0.1:1 BEND_LIB=$out bend main.bend 2>&1 | tail -1)"

echo "PASS: $pass / $total"
[ "$pass" = "$total" ]

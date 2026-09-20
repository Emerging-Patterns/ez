#!/usr/bin/env bash
# Drives the `ez` binary through a whole project: init, add a git package that
# was never published, lock, fetch into a fresh BEND_LIB, check, run, remove.
#   ./tests/cli.sh
set -u
# the gate exports BEND_LIB for its own lanes; a test picks its own
unset BEND_LIB
cd "$(dirname "$0")/.."
ez=$PWD
root=$(mktemp -d)
trap 'st=$?; [ -n "${daemon:-}" ] && kill "$daemon" 2>/dev/null; rm -rf "$root"; exit $st' EXIT
pass=0; total=0
check() { # name, expected, observed
  total=$((total + 1))
  if [ "$2" = "$3" ]; then pass=$((pass + 1)); else
    echo "FAIL: $1"; diff <(echo "$2") <(echo "$3") | sed 's/^/  /'
  fi
}

[ -x bin/ez.bin ] || ./build.sh >/dev/null

mkdir -p "$root/upstream/src"
cat > "$root/upstream/src/lib.bend" <<'EOF'
import Base

# double the number
def double(+x: U32) -> U32:
  (x * 2 : U32)
EOF
git -C "$root/upstream" init -q
git -C "$root/upstream" add -A
git -C "$root/upstream" -c user.email=t@t -c user.name=t commit -q -m init
rev=$(git -C "$root/upstream" rev-parse HEAD)
mkdir -p "$root/srv"
git clone -q --bare "$root/upstream" "$root/srv/upstream.git"
git -C "$root/srv/upstream.git" config uploadpack.allowAnySHA1InWant true
port=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1]); s.close()')
git daemon --reuseaddr --listen=127.0.0.1 --port="$port" --base-path="$root/srv" --export-all >/dev/null 2>&1 &
daemon=$!
for _ in $(seq 50); do git ls-remote "git://127.0.0.1:$port/upstream.git" >/dev/null 2>&1 && break; sleep 0.1; done

mkdir -p "$root/app"
cd "$root/app"

"$ez/ez/ez" init myapp main.bend
check "init writes a ledger" \
  "[package]
name = \"myapp\"
entry = \"main.bend\"" \
  "$(cat ez.toml)"

"$ez/ez/ez" add "git://127.0.0.1:$port/upstream.git" "$rev" src/lib.bend >/dev/null 2>&1
hash=$(grep '^hash' ez.toml | sed 's/.*"\(.*\)"/\1/')
check "add records the package under its name" \
  "[deps.lib]
hash = \"$hash\"
git = \"git://127.0.0.1:$port/upstream.git\"
rev = \"$rev\"
entry = \"src/lib.bend\"" \
  "$(sed -n '/\[deps.lib\]/,$p' ez.toml)"

cat > main.bend <<EOF
import Base
import $hash/lib.bend as L

def main() -> U32:
  L.double(21)
EOF

"$ez/ez/ez" lock >/dev/null 2>&1
check "lock records the git source" "git $rev" \
  "$(python3 -c 'import json,sys; s=json.load(open("ez.lock.json"))["packages"][sys.argv[1]]["source"]; print(s["kind"], s["rev"])' "$hash")"

rm -rf .ez/lib
"$ez/ez/ez" fetch >/dev/null 2>&1
check "fetch fills BEND_LIB from the lock alone" "0" \
  "$([ -f ".ez/lib/$hash/lib.bend" ]; echo $?)"

kill "$daemon" 2>/dev/null; daemon=
check "check passes with the git remote gone" "0" \
  "$("$ez/ez/ez" check >/dev/null 2>&1; echo $?)"
check "run gives the program's answer" "42" \
  "$("$ez/ez/ez" run 2>/dev/null | tail -1)"

mkdir -p src/tests
cat > src/tests/ok.bend <<'EOF'
import Base

def main() -> IO(Unit):
  IO.print("ok one")

#|ok one
EOF
check "test passes a file that prints its trailer" "PASS: 1 / 1" \
  "$("$ez/ez/ez" test --js-only 2>&1 | tail -1)"

cat > src/tests/bad.bend <<'EOF'
import Base

def main() -> IO(Unit):
  IO.print("ok one")

#|ok two
EOF
check "test fails a file that does not" "1" \
  "$("$ez/ez/ez" test --js-only >/dev/null 2>&1; echo $?)"
rm src/tests/bad.bend

check "doctor passes a project with nothing wrong" "0" \
  "$("$ez/ez/ez" doctor >/dev/null 2>&1; echo $?)"

"$ez/ez/ez" remove lib
check "remove drops it from the ledger" "0" \
  "$(grep -c 'deps.lib' ez.toml || true)"
check "and leaves the package stanza alone" "myapp" \
  "$(grep '^name' ez.toml | sed 's/.*"\(.*\)"/\1/')"

check "doctor reports a hash the ledger no longer names" "1" \
  "$("$ez/ez/ez" doctor 2>&1 | grep -c "^drift: $hash is imported")"
check "and that drift fails the command" "1" \
  "$("$ez/ez/ez" doctor >/dev/null 2>&1; echo $?)"

check "an unknown subcommand fails" "1" \
  "$("$ez/ez/ez" nonsense >/dev/null 2>&1; echo $?)"

echo "PASS: $pass / $total"
[ "$pass" = "$total" ]

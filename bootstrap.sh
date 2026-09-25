#!/bin/sh
# bootstrap.sh: fill BEND_LIB from ez.lock.toml without ez, so a clone can
# build ez without nix. ez fetches its own dependencies with `ez fetch`, but
# that needs ez built, and ez's build needs them first. This is the one
# helper script in the repo, and it does only that: for every git package in
# the lock, fetch the pinned rev, copy the package's files, check each file's
# sha256 and the package's 0x name, and write the manifest the way ez does.
#
#   sh bootstrap.sh [lock]        (lock defaults to ez.lock.toml)
#
# Needs git, awk and sha256sum (or shasum). BEND_LIB defaults to .ez/lib.
set -eu

lock=${1:-ez.lock.toml}
lib=${BEND_LIB:-.ez/lib}

die() { printf 'bootstrap: %s\n' "$*" >&2; exit 1; }

if command -v sha256sum >/dev/null 2>&1; then
  sum() { sha256sum <"$1" | cut -d' ' -f1; }
elif command -v shasum >/dev/null 2>&1; then
  sum() { shasum -a 256 <"$1" | cut -d' ' -f1; }
else
  die "needs sha256sum or shasum"
fi
command -v git >/dev/null 2>&1 || die "needs git"
[ -f "$lock" ] || die "no lock at $lock"

mkdir -p "$lib"
tmp=$(mktemp -d)
stage="$lib/.bootstrap.$$"
trap 'rm -rf "$tmp" "$stage"' EXIT
trap 'exit 1' INT TERM

# the lock, flattened: `<hash> src <key> <value>` for each source key and
# `<hash> file <path> <sum>` for each file. A package's tables are headed
# `[packages.0x<hash>.source]`, or `[packages."0x<hash>".source]` in a lock
# written before ez used eztoml 0.4; the tables a dotted header implies
# (`[packages]`, `[packages.0x<hash>]`) hold no key, and are passed over.
awk '
  /^\[packages\."?0x[0-9a-f]+"?\.(source|files)\]$/ {
    match($0, /0x[0-9a-f]+/); h = substr($0, RSTART, RLENGTH)
    t = ($0 ~ /\.source\]$/) ? "src" : "file"
    next
  }
  /^\[/ { h = ""; next }
  h != "" && /=/ {
    k = $0; sub(/[ \t]*=.*/, "", k); gsub(/"/, "", k)
    v = $0; sub(/^[^=]*=[ \t]*/, "", v); gsub(/"/, "", v)
    print h, t, k, v
  }
' "$lock" >"$tmp/table"

src() { awk -v h="$1" -v k="$2" '$1 == h && $2 == "src" && $3 == k { print $4 }' "$tmp/table"; }

cut -d' ' -f1 "$tmp/table" | sort -u >"$tmp/hashes"
while read -r h; do
  # the manifest ez writes: `<sum> <path>` per file, sorted by path
  awk -v h="$h" '$1 == h && $2 == "file" { print $4, $3 }' "$tmp/table" |
    LC_ALL=C sort -t' ' -k2 >"$tmp/manifest"
  if [ -f "$lib/$h/manifest" ] && cmp -s "$tmp/manifest" "$lib/$h/manifest"; then
    continue
  fi
  kind=$(src "$h" kind)
  [ "$kind" = git ] || die "$h is kind '$kind'; this script only fetches git pins (use ez fetch)"
  url=$(src "$h" url); rev=$(src "$h" rev); root=$(src "$h" root)
  printf 'bootstrap: %s from %s at %s\n' "$h" "$url" "$rev" >&2
  rm -rf "$tmp/work" "$stage"
  git init -q "$tmp/work"
  git -C "$tmp/work" fetch -q --depth 1 "$url" "$rev" || die "$h: git fetch $url $rev failed"
  git -C "$tmp/work" checkout -q "$rev"
  while read -r want path; do
    from="$tmp/work/$root/$path"
    [ -f "$from" ] || die "$h: $path is not in $url at $rev"
    [ "$(sum "$from")" = "$want" ] || die "$h: $path does not match its sha256 in $lock"
    mkdir -p "$stage/$(dirname "$path")"
    cp "$from" "$stage/$path"
  done <"$tmp/manifest"
  cp "$tmp/manifest" "$stage/manifest"
  # ez names a package "0x" and the first 32 hex digits of its manifest's sha256
  case $(sum "$stage/manifest") in
    "${h#0x}"*) ;;
    *) die "$h: the manifest does not hash to this name" ;;
  esac
  rm -rf "${lib:?}/$h"
  mv "$stage" "$lib/$h"
done <"$tmp/hashes"

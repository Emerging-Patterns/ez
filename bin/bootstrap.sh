#!/usr/bin/env bash
# Fills BEND_LIB from ez.lock.toml without ez.
#
# `ez fetch` is Bend now, and ez's own Bend imports sha256 from a package that
# lives in BEND_LIB, so on a fresh checkout there is nothing to run it with.
# This is that one bootstrap, and nothing else should use it: it reads the lock
# ez wrote, fetches each package, and checks every file against the sha256 the
# lock records, the same rule `ez fetch` and nix/bend-lib.nix apply.
#
#   BEND_LIB=$PWD/.ez/lib bin/bootstrap.sh [ez.lock.toml]
set -eu
cd "$(dirname "$0")/.."
lock=${1:-ez.lock.toml}
lib=${BEND_LIB:-$PWD/.ez/lib}

# every package the lock records, as `<hash> <kind> <url> <rev> <root>`
packages() {
  awk '
    /^\[packages\."/ {
      at = $0; sub(/^\[packages\."/, "", at); sub(/"\..*$/, "", at)
      if (at != hash) { if (hash != "") print hash, kind, url, rev, root; hash = at
        kind = "hub"; url = ""; rev = ""; root = "." }
      next
    }
    /^[a-zA-Z]+ = "/ {
      key = $1; val = $0; sub(/^[^=]*= "/, "", val); sub(/"$/, "", val)
      if (key == "kind") kind = val
      if (key == "url") url = val
      if (key == "rev") rev = val
      if (key == "root") root = val
    }
    END { if (hash != "") print hash, kind, url, rev, root }
  ' "$lock"
}

# every file of one package, as `<path> <sha256>`
files() { # hash
  awk -v want="[packages.\"$1\".files]" '
    $0 == want { on = 1; next }
    /^\[/ { on = 0 }
    on && /= "/ {
      at = $0; sub(/ = .*$/, "", at); gsub(/"/, "", at)
      sum = $0; sub(/^.*= "/, "", sum); sub(/"$/, "", sum)
      print at, sum
    }
  ' "$lock"
}

hub=$(awk '/^\[lock\]$/ { on = 1; next } /^\[/ { on = 0 }
  on && /^hub = "/ { sub(/^hub = "/, ""); sub(/"$/, ""); print }' "$lock")

put() { # dst sha256
  got=$(sha256sum "$1" | cut -d' ' -f1)
  [ "$got" = "$2" ] || { echo "$1: $got, want $2" >&2; exit 1; }
}

while read -r hash kind url rev root; do
  rm -rf "${lib:?}/$hash"
  mkdir -p "$lib/$hash"
  if [ "$kind" = git ]; then
    work=$lib/.work-$hash
    rm -rf "$work"; mkdir -p "$work"
    git init -q "$work"
    git -C "$work" fetch -q --depth 1 "$url" "$rev"
    git -C "$work" checkout -q "$rev"
  fi
  : > "$lib/$hash/manifest"
  while read -r at sum; do
    mkdir -p "$lib/$hash/$(dirname "$at")"
    if [ "$kind" = git ]; then cp "$work/$root/$at" "$lib/$hash/$at"
    else curl -fsS "$hub/$hash/$at" -o "$lib/$hash/$at"
    fi
    put "$lib/$hash/$at" "$sum"
    printf '%s %s\n' "$sum" "$at" >> "$lib/$hash/manifest"
  done < <(files "$hash" | sort -k1,1)
  if [ "$kind" = git ]; then rm -rf "$work"; fi
  echo "$hash $kind"
done < <(packages)

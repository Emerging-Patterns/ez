#!/usr/bin/env bash
# Builds the binary people run: bin/ez.bin, behind the ez/ez script, linked
# into ~/.local/bin as `ez`.
set -eu
cd "$(dirname "$0")"
mkdir -p bin "$HOME/.local/bin"
export BEND_LIB="${BEND_LIB:-$PWD/.ez/lib}"
bend ez/main.bend -o bin/ez.bin
ln -sfn "$PWD/ez/ez" "$HOME/.local/bin/ez"
echo "built bin/ez.bin -> ~/.local/bin/ez"

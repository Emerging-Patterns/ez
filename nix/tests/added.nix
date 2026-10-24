# `ez add` then an offline nix build, with no `ez lock` between (EZ-DOC-6).
#
# A project whose staged main.bend already imports a git package by its hash
# runs `ez add` on that package, a repository beside it, in the sandbox, with
# no hub and no network. The lock `ez add` writes must be ./added/ez.lock.toml
# byte for byte, and mkPackage builds the program from that same lock with no
# network: bend-lib.nix's fetchgit is swapped for a fixed-output derivation
# that lays the dependency's file and is checked against the narHash the lock
# records. So the build passes only when `ez add` writes the lock the build
# needs: an add that leaves the lock as it was fails the `cmp`.
#
# The Bend sources are strings here, not committed `.bend` files, because
# `ez lock` reads every `.bend` file git tracks as a root of ez's own lock (see
# named.nix). The dependency's commit is made with a fixed author, committer
# and date, so its rev, and the lock, are the same on every machine.
# ./added/ez.toml is the ledger before the add; `ez add` writes the lock that
# ./added/ez.lock.toml holds.
{ pkgs, bend, ez, nativeBuildInputs ? [ ] }:

let
  lib = pkgs.lib;
  src = ./added;
  lockFile = src + "/ez.lock.toml";
  doc = builtins.fromTOML (builtins.readFile lockFile);

  dep = "# a package ez add pins from a repository beside the project\nimport Base\n\ndef answer() -> U32:\n  42\n";
  depFile = builtins.toFile "lib.bend" dep;
  hash = "0xfe8120688511cf87c1f48ab713570f6c";
  main = builtins.toFile "main.bend"
    "# a program importing a package ez add pinned\nimport Base\nimport ${hash}/lib.bend as Lib\n\ndef main() -> U32:\n  Lib.answer()\n";

  # the lock's git package, laid as fetchgit would lay the checkout and
  # checked against the narHash the lock records
  fetchgit = { url, rev, hash, name, ... }:
    assert url == "../dep";
    pkgs.runCommand name {
      outputHashMode = "recursive";
      outputHashAlgo = "sha256";
      outputHash = hash;
    } ''
      mkdir -p $out
      cp ${depFile} $out/lib.bend
    '';

  ezLib = import ../lib.nix {
    inherit bend;
    pkgs = pkgs // {
      callPackage = f: args: pkgs.callPackage f ({ inherit fetchgit; } // args);
    };
  };

  app = (ezLib.mkPackage { inherit bend src nativeBuildInputs; }).overrideAttrs {
    postUnpack = ''cp ${main} "$sourceRoot/main.bend"'';
  };
in
assert doc.packages ? ${hash};
pkgs.runCommand "add-then-build" { nativeBuildInputs = [ pkgs.git ]; } ''
  export HOME=$TMPDIR BEND_LIB=$TMPDIR/lib BEND_HUB=http://127.0.0.1:1
  export GIT_AUTHOR_NAME=ez GIT_AUTHOR_EMAIL=ez@example.invalid
  export GIT_COMMITTER_NAME=ez GIT_COMMITTER_EMAIL=ez@example.invalid
  export GIT_AUTHOR_DATE='2026-01-01T00:00:00Z' GIT_COMMITTER_DATE='2026-01-01T00:00:00Z'
  mkdir -p $TMPDIR/dep $TMPDIR/app

  cd $TMPDIR/dep
  git init -q -b main
  cp ${depFile} lib.bend
  git add lib.bend
  git commit -q -m dep

  cd $TMPDIR/app
  git init -q -b main
  cp ${src}/ez.toml ez.toml
  chmod u+w ez.toml
  cp ${main} main.bend
  git add ez.toml main.bend
  ${ez}/bin/ez add ../dep main lib.bend
  grep -qx '\[deps.dep\]' ez.toml || { cat ez.toml; exit 1; }
  cmp ez.lock.toml ${lockFile} || { diff ez.lock.toml ${lockFile}; exit 1; }

  got=$(${app}/bin/added-app 2>&1)
  printf '%s\n' "$got" | grep -qx 42 || { echo "added-app said: $got"; exit 1; }
  echo ok > $out
''

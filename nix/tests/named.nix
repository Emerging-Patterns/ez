# A project whose dependency imports another package by its hub name, built
# by mkPackage with no network at all. main.bend imports named-dependency by
# its 0x hash, and that package's doc.bend imports
# `named-library@0.1.0.0/lib.bend`, which the lock records in `[names]`. bend
# resolves that import only through `BEND_LIB/names/named-library@0.1.0.0`, so
# the build passes only when bend-lib.nix lays the names files `ez fetch` lays.
#
# ./named holds the ledger and the lock `ez lock` wrote against a local hub
# (`python3 -m http.server` over the two packages below; both files name it at
# 127.0.0.1:1 since). The Bend sources are strings here, not committed `.bend`
# files, because `ez lock` reads every `.bend` file git tracks as a root of
# ez's own lock. fetchurl is swapped for a lookup in `hub` that checks the
# sha256 the lock records, so the sandbox needs no hub and no fetch.
{ pkgs, bend, nativeBuildInputs ? [ ] }:

let
  lib = pkgs.lib;
  src = ./named;
  lockFile = src + "/ez.lock.toml";
  doc = builtins.fromTOML (builtins.readFile lockFile);

  # the hub's files, by the path bend-lib.nix asks for under the lock's hub
  hub = {
    "0x5c91a927dfd42412df799159c017e177/lib.bend" =
      "# the library named-dependency imports by its hub name\nimport Base\n\ndef answer() -> U32:\n  42\n";
    "0x6488ec0538085e3b469f5210e33890dd/doc.bend" =
      "# a package that imports another by its hub name, not its hash\nimport Base\nimport named-library@0.1.0.0/lib.bend as L\n\ndef answer() -> U32:\n  L.answer()\n";
  };

  main = builtins.toFile "main.bend"
    "# a program whose dependency imports another package by its hub name\nimport Base\nimport 0x6488ec0538085e3b469f5210e33890dd/doc.bend as D\n\ndef main() -> U32:\n  D.answer()\n";

  fetchurl = { url, sha256, name }:
    let
      at = lib.removePrefix "${doc.lock.hub}/" url;
      text = hub.${at} or (throw "named fixture: the hub has no ${url}");
      got = builtins.hashString "sha256" text;
    in
    if got != sha256 then
      throw "named fixture: ${url} hashes to ${got}, and the lock says ${sha256}"
    else
      builtins.toFile name text;

  # lib.nix as a flake gets it, except that bend-lib.nix fetches from `hub`
  ez = import ../lib.nix {
    inherit bend;
    pkgs = pkgs // {
      callPackage = f: args: pkgs.callPackage f ({ inherit fetchurl; } // args);
    };
  };

  tree = ez.bendLib lockFile;
  app = (ez.mkPackage { inherit bend src nativeBuildInputs; }).overrideAttrs {
    postUnpack = ''cp ${main} "$sourceRoot/main.bend"'';
  };

  # each names file as `ez fetch` writes it: the hash and a newline
  expect = lib.concatStrings (lib.mapAttrsToList (nv: hash: ''
    printf '%s\n' ${lib.escapeShellArg hash} | cmp - ${tree}/names/${lib.escapeShellArg nv}
  '') doc.names);
in
assert doc.names != { };
pkgs.runCommand "named-imports" { } ''
  ${expect}
  [ "$(ls ${tree}/names | wc -l)" = ${toString (builtins.length (builtins.attrNames doc.names))} ]
  got=$(${app}/bin/named-app 2>&1)
  printf '%s\n' "$got" | grep -qx 42 || { echo "named-app said: $got"; exit 1; }
  echo ok > $out
''

# A BEND_LIB tree built from ez.lock.json alone. Every file is one fixed-output
# fetchurl keyed by the sha256 the hub manifest already records, so the sandbox
# needs no network and `bend` never calls the hub.
#
#   bendLib = pkgs.callPackage ./nix/bend-lib.nix { } ./ez.lock.json;
#   ... buildPhase = "BEND_LIB=${bendLib} bend main.bend -o app";
{ lib, fetchurl, runCommand }:

lockFile:

let
  lock = builtins.fromJSON (builtins.readFile lockFile);
  # one fetchurl per file: <hub>/<0xhash>/<path>, checked against the manifest's sha256
  file = hash: at: sha256:
    fetchurl {
      url = "${lock.hub}/${hash}/${at}";
      inherit sha256;
      name = "bend-${lib.removePrefix "0x" hash}-${builtins.baseNameOf at}";
    };
  copy = hash: at: sha256: ''
    mkdir -p "$out/${hash}/$(dirname ${lib.escapeShellArg at})"
    cp ${file hash at sha256} "$out/${hash}/${at}"
  '';
  copies = lib.concatLists (lib.mapAttrsToList
    (hash: files: lib.mapAttrsToList (copy hash) files)
    lock.packages);
in
runCommand "bend-lib" { passthru = { inherit lock; }; }
  (lib.concatStrings ([ "mkdir -p $out\n" ] ++ copies))

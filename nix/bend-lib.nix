# A BEND_LIB tree built from ez.lock.toml alone. The sandbox needs no network
# and `bend` never calls the hub.
#
#   bendLib = pkgs.callPackage ./nix/bend-lib.nix { } ./ez.lock.toml;
#   ... buildPhase = "BEND_LIB=${bendLib} bend main.bend -o app";
#
# A hub package is one fixed-output fetchurl per file, keyed by the sha256 its
# manifest already records. A git package is one fetchgit of the pinned rev, and
# its files are taken from the checkout at the paths the manifest names, which
# are relative to the package's own root: the entry file's directory, unless a
# module of it was reached through `..` and re-rooted the package above that.
{ lib, fetchurl, fetchgit, runCommand }:

lockFile:

let
  doc = builtins.fromTOML (builtins.readFile lockFile);

  manifest = files:
    lib.concatStrings (map (p: "${files.${p}} ${p}\n") (lib.naturalSort (builtins.attrNames files)));

  hubFile = hash: at: sha256: fetchurl {
    url = "${doc.lock.hub}/${hash}/${at}";
    inherit sha256;
    name = "bend-${lib.removePrefix "0x" hash}-${builtins.baseNameOf at}";
  };

  # the git source is fetched once; each file is checked on unpack against the
  # lock, so a rev that no longer matches fails the build instead of the check.
  # The digest is sha256 of the file's bytes: the one `bend --publish` and the
  # hub name a file by, and the one ez's Sha.hex takes of a text's UTF-8.
  gitSrc = hash: source: fetchgit {
    inherit (source) url rev;
    name = "bend-${lib.removePrefix "0x" hash}-src";
    hash = source.narHash;
  };

  pkg = hash: entry:
    let files = entry.files; in
    if entry.source.kind == "git" then ''
      mkdir -p "$out/${hash}"
      from=${gitSrc hash entry.source}/${entry.source.root}
      ${lib.concatStrings (lib.mapAttrsToList (at: sha256: ''
        mkdir -p "$out/${hash}/$(dirname ${lib.escapeShellArg at})"
        cp "$from/${at}" "$out/${hash}/${at}"
        got=$(sha256sum "$out/${hash}/${at}" | cut -d' ' -f1)
        [ "$got" = "${sha256}" ] || { echo "${hash}/${at}: got $got, want ${sha256}"; exit 1; }
      '') files)}
      printf '%s' ${lib.escapeShellArg (manifest files)} > "$out/${hash}/manifest"
    '' else ''
      ${lib.concatStrings (lib.mapAttrsToList (at: sha256: ''
        mkdir -p "$out/${hash}/$(dirname ${lib.escapeShellArg at})"
        cp ${hubFile hash at sha256} "$out/${hash}/${at}"
      '') files)}
    '';
  # `[tools.*]` is a CLI pin. This tree is `[packages.*]` only.
in
runCommand "bend-lib" { passthru = { lock = doc; }; } (''
  mkdir -p "$out"
'' + lib.concatStrings (lib.mapAttrsToList pkg (doc.packages or { })))

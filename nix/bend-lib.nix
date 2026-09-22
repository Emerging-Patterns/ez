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
{ lib, fetchurl, fetchgit, runCommand, python3 }:

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
  # The digest is Bend's Sha.hex: the file read as UTF-8 text, each character
  # folded to Char.to_u32(c) & 0xff, then sha256 of those bytes. On ASCII the
  # fold is the file's own bytes, so it agrees with sha256sum.
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
        got=$(bend_sha256 "$out/${hash}/${at}")
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
runCommand "bend-lib" {
  passthru = { lock = doc; };
  nativeBuildInputs = [ python3 ];
} (''
  mkdir -p "$out"
  # low 8 bits of each Unicode scalar, then sha256. CR is left as a character.
  bend_sha256() {
    python3 -c 'import hashlib,sys; t=open(sys.argv[1],encoding="utf-8",newline="").read(); print(hashlib.sha256(bytes(ord(c)&255 for c in t)).hexdigest(), end="")' "$1"
  }
'' + lib.concatStrings (lib.mapAttrsToList pkg (doc.packages or { })))

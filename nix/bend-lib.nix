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
#
# Every name the lock's `[names]` table records is laid as `ez fetch` lays it:
# `names/<name>@<version>` holding the `0x` hash and a newline, the file bend
# reads a named import's hash from, so a package that imports another by its
# hub name resolves here too (EZ-HUB-4). A name or hash bend would not read
# back fails the evaluation, as `ez fetch` refuses it.
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
  # The digest is sha256 of the file's bytes: the one `bend --publish` and the
  # hub name a file by, and the one ez's Sha.hex takes of a text's UTF-8. A
  # lock an older ez wrote (a tool's, say) may instead hold that ez's digest:
  # each character's low eight bits, then sha256. Either is accepted, so such a
  # lock still builds; on ASCII the two are the same.
  # Submodules are not fetched: ez weighs the checkout without them, so the
  # narHash it records is that tree's, and fetchgit fetches them by default.
  gitSrc = hash: source: fetchgit {
    inherit (source) url rev;
    fetchSubmodules = false;
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
        [ "$got" = "${sha256}" ] || got=$(folded "$out/${hash}/${at}")
        [ "$got" = "${sha256}" ] || { echo "${hash}/${at}: got $got, want ${sha256}"; exit 1; }
      '') files)}
      printf '%s' ${lib.escapeShellArg (manifest files)} > "$out/${hash}/manifest"
    '' else ''
      ${lib.concatStrings (lib.mapAttrsToList (at: sha256: ''
        mkdir -p "$out/${hash}/$(dirname ${lib.escapeShellArg at})"
        cp ${hubFile hash at sha256} "$out/${hash}/${at}"
      '') files)}
    '';
  # bend's NAMED rule and a `0x` name, the pair `ez fetch` lays (src/pkg/pkg.bend
  # `name.ok`, src/lock/lock.bend `hash.ok`)
  num = "(0|[1-9][0-9]*)";
  nameOk = nv: builtins.match "[a-z][a-z0-9-]{0,63}@${num}\\.${num}\\.${num}\\.${num}" nv != null;
  hashOk = hash: builtins.match "0x[0-9a-f]{32}" hash != null;

  name = nv: hash:
    if !(nameOk nv) then
      throw "bend-lib.nix: the lock names ${nv}, which bend would not read as <name>@<version>"
    else if !(builtins.isString hash && hashOk hash) then
      throw "bend-lib.nix: the lock names ${nv} as ${builtins.toJSON hash}, which is not a 0x name"
    else ''
      printf '%s\n' ${lib.escapeShellArg hash} > "$out/names/"${lib.escapeShellArg nv}
    '';

  names = doc.names or { };

  # `[tools.*]` is a CLI pin. This tree is `[packages.*]` and `[names]` only.
in
runCommand "bend-lib" {
  passthru = { lock = doc; };
  nativeBuildInputs = [ python3 ];
} (''
  mkdir -p "$out"
  # the digest an older ez wrote: low 8 bits of each Unicode scalar, then sha256
  folded() {
    python3 -c 'import hashlib,sys; t=open(sys.argv[1],encoding="utf-8",newline="").read(); print(hashlib.sha256(bytes(ord(c)&255 for c in t)).hexdigest(), end="")' "$1"
  }
'' + lib.concatStrings (lib.mapAttrsToList pkg (doc.packages or { }))
  + lib.optionalString (names != { }) ''
    mkdir -p "$out/names"
  '' + lib.concatStrings (lib.mapAttrsToList name names))

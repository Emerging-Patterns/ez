# Package builds and checks for a Bend flake. Taken from `lib.${system}`.
#
#   ez = inputs.ez.lib.${system};
#   bolt = ez.mkPackage { inherit bend; src = self; wrapFlags = [ "--gpu" "off" ]; };
{ pkgs }:

let
  lib = pkgs.lib;
  llvm = pkgs.llvmPackages_19;

  # clang 19, unwrapped, with the system's ld and dynamic linker, so a GPU
  # build can still load the system libstdc++.
  bend-cc = pkgs.writeShellScriptBin "bend-cc" ''
    exec ${llvm.clang-unwrapped}/bin/clang \
      -resource-dir ${llvm.clang}/resource-root \
      --ld-path=/usr/bin/ld \
      -Wl,--dynamic-linker=/lib64/ld-linux-x86-64.so.2 "$@"
  '';

  # An ez.lock.toml as a BEND_LIB store path.
  bendLib = lock: pkgs.callPackage ./bend-lib.nix { } lock;

  nonEmpty = v: v != null && v != "";

  ledger = src:
    let doc = builtins.fromTOML (builtins.readFile (src + "/ez.toml"));
    in doc.package or { };

  # The file `bend -o` builds: `bin` when the ledger names one, otherwise
  # `entry`, otherwise `main.bend`. `entry` here is that file, overridden.
  builtFile = src: entry:
    let pkg = ledger src; in
    if nonEmpty entry then entry
    else if nonEmpty (pkg.bin or "") then pkg.bin
    else if nonEmpty (pkg.entry or "") then pkg.entry
    else "main.bend";

  pkgName = src: pname:
    let pkg = ledger src; in
    if nonEmpty pname then pname
    else if nonEmpty (pkg.name or "") then pkg.name
    else "app";

  pkgVersion = src: version:
    let pkg = ledger src; in
    if nonEmpty version then version
    else if nonEmpty (toString (pkg.version or "")) then toString pkg.version
    else "0.1.0";

  # An explicit lock, or src/ez.lock.toml when that file is in the tree.
  lockOf = src: lock:
    if lock != null then lock
    else if builtins.pathExists (src + "/ez.lock.toml") then src + "/ez.lock.toml"
    else null;

  bendLibOf = src: lock:
    let file = lockOf src lock; in
    if file == null then null else bendLib file;

  withBendLib = tree: attrs:
    attrs // lib.optionalAttrs (tree != null) { BEND_LIB = tree; };

  copyTree = src: body: ''
    cp -r ${src} src
    chmod -R u+w src
    cd src
    ${body}
    echo ok > $out
  '';

  # bend, then extraPath, on PATH. Each wrapFlags entry is one argument.
  wrapArgs = bend: extraPath: wrapFlags: wrapEnv: defaultWrapEnv:
    lib.concatStringsSep " " (
      [
        "--prefix" "PATH" ":"
        (lib.escapeShellArg (lib.makeBinPath ([ bend ] ++ extraPath)))
      ]
      ++ map (flag: "--add-flag ${lib.escapeShellArg flag}") wrapFlags
      ++ lib.mapAttrsToList (n: v:
        "--set ${lib.escapeShellArg n} ${lib.escapeShellArg (toString v)}") wrapEnv
      ++ lib.mapAttrsToList (n: v:
        "--set-default ${lib.escapeShellArg n} ${lib.escapeShellArg (toString v)}") defaultWrapEnv
    );
in
{
  inherit bend-cc bendLib;

  # Build the program the ledger names and wrap it onto $out/bin/<pname>.
  # PATH starts with bend. wrapFlags are appended. wrapEnv is `--set`;
  # defaultWrapEnv is `--set-default`. extraPath is appended to that PATH.
  # extraInstall runs after the wrap (a second binary, for one).
  mkPackage = {
    bend,
    src,
    wrapFlags ? [ ],
    pname ? null,
    version ? null,
    entry ? null,
    lock ? null,
    wrapEnv ? { },
    defaultWrapEnv ? { },
    extraPath ? [ ],
    nativeBuildInputs ? [ ],
    meta ? { },
    extraInstall ? "",
  }:
    let
      name = pkgName src pname;
      ver = pkgVersion src version;
      file = builtFile src entry;
      tree = bendLibOf src lock;
    in
    pkgs.stdenv.mkDerivation (withBendLib tree {
      pname = name;
      version = ver;
      inherit src;
      nativeBuildInputs = [ bend ] ++ nativeBuildInputs ++ [ pkgs.makeWrapper ];
      meta = { mainProgram = name; } // meta;
      buildPhase = ''
        bend ${lib.escapeShellArg file} -o ${lib.escapeShellArg "${name}.bin"}
      '';
      installPhase = ''
        mkdir -p $out/bin
        cp ${lib.escapeShellArg "${name}.bin"} "$out/bin/${name}"
        wrapProgram "$out/bin/${name}" ${wrapArgs bend extraPath wrapFlags wrapEnv defaultWrapEnv}
        ${extraInstall}
      '';
    });

  # `ez test` in a writable copy of src. EZ_DEADLINE defaults to 0.
  # extraFlags are further arguments (`--js-only`, `--unit-only`).
  # When src has ez.lock.toml, BEND_LIB is that tree.
  mkProofs = {
    ez,
    src,
    name ? "proofs",
    extraFlags ? [ ],
    deadline ? "0",
  }:
    pkgs.runCommand name
      (withBendLib (bendLibOf src null) {
        nativeBuildInputs = [ ez ];
        EZ_DEADLINE = toString deadline;
      })
      (copyTree src "ez test ${lib.escapeShellArgs extraFlags}");

  # `bolt` in a writable copy of src.
  # When src has ez.lock.toml, BEND_LIB is that tree.
  mkLint = { bolt, src, name ? "lint" }:
    pkgs.runCommand name
      (withBendLib (bendLibOf src null) {
        nativeBuildInputs = [ bolt ];
      })
      (copyTree src "bolt");

  # CC=bend-cc and BEND_LIB=$PWD/.ez/lib. bend-cc belongs in packages.
  # extraHook runs after those exports.
  mkShell = { packages, extraHook ? "" }:
    pkgs.mkShellNoCC {
      inherit packages;
      shellHook = ''
        export CC=bend-cc
        export BEND_LIB=$PWD/.ez/lib
        ${extraHook}
      '';
    };
}

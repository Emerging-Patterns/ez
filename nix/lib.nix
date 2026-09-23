# Package builds and checks for a Bend flake. Taken from `lib.${system}`.
#
#   ez = inputs.ez.lib.${system};
#   bolt = ez.toolPackage { name = "bolt"; inherit src; };
#   lint = ez.mkLint { src = self; };
{ pkgs, bend ? null }:

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

  # An explicit BEND_LIB store path wins. Otherwise the tree of `lock`, or of
  # src/ez.lock.toml when that file is present. Otherwise null, and BEND_LIB
  # is unset.
  bendLibFor = given: src: lock:
    if given != null then given else bendLibOf src lock;

  withBendLib = tree: attrs:
    attrs // lib.optionalAttrs (tree != null) { BEND_LIB = tree; };

  defaultBend = bend;

  lockDoc = src: lock:
    let file = lockOf src lock; in
    if file == null then { } else builtins.fromTOML (builtins.readFile file);

  # The `[tools.<name>]` table of a lock, or null when the lock has none.
  toolPin = src: lock: name:
    (lockDoc src lock).tools.${name} or null;

  # `bin` when the pin names one, otherwise `entry`, otherwise null so
  # mkPackage reads the tool's own ledger.
  toolFile = pin:
    let
      bin = pin.bin or "";
      entry = pin.entry or "";
    in
    if bin != "" then bin else if entry != "" then entry else null;

  # The checkout `fetchgit` rebuilds from the pin. `root` is the directory
  # inside it the tool's paths are written from.
  toolSrc = pin:
    let
      fetched = pkgs.fetchgit {
        url = pin.git;
        rev = pin.rev;
        hash = pin.narHash;
      };
      root = pin.root or ".";
    in
    if root == "." || root == "" then fetched else fetched + "/${root}";

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
rec {
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

  # `ez prove` in a writable copy of src: `bend` on every PROOF.bend, passing
  # only when each one's first line is `All terms check.` It takes no flags.
  # `lock` is an explicit lock path, as in mkPackage. `bendLib`, when non-null,
  # is the store path used as BEND_LIB. Precedence: `bendLib`, else
  # `bendLibOf src lock`, else no BEND_LIB.
  #
  #   checks.${system}.proofs = inputs.ez.lib.${system}.mkProofs {
  #     ez = inputs.ez.packages.${system}.default;
  #     src = self;
  #     name = "…-proofs";
  #   };
  mkProofs = {
    ez,
    src,
    name ? "proofs",
    lock ? null,
    bendLib ? null,
    # accepted and ignored: they were `ez test`'s flags and budget, and a
    # caller written against the old signature still evaluates
    extraFlags ? [ ],
    deadline ? null,
  }:
    pkgs.runCommand name
      (withBendLib (bendLibFor bendLib src lock) {
        nativeBuildInputs = [ ez ];
      })
      (copyTree src "ez prove");

  # A locked `[tools.<name>]` built with mkPackage. `bend` defaults to the
  # one this lib was imported with. The derivation's name is the pin's name.
  toolPackage = {
    name,
    src,
    bend ? defaultBend,
    lock ? null,
    wrapFlags ? [ ],
    version ? null,
    entry ? null,
    extraPath ? [ ],
    nativeBuildInputs ? [ llvm.clang ],
    wrapEnv ? { },
    defaultWrapEnv ? { },
    meta ? { },
    extraInstall ? "",
  }:
    let
      pin = toolPin src lock name;
      file = if entry != null then entry else if pin == null then null else toolFile pin;
    in
    if pin == null then
      throw "ez.lock.toml has no [tools.${name}]"
    else if bend == null then
      throw "toolPackage needs bend to build ${name}"
    else mkPackage {
      inherit bend wrapFlags version extraPath nativeBuildInputs wrapEnv
        defaultWrapEnv meta extraInstall;
      pname = name;
      src = toolSrc pin;
      entry = file;
    };

  # Every locked tool, in the order the lock names them.
  devPackages = src:
    map (name: toolPackage { inherit name src; })
      (builtins.attrNames ((lockDoc src null).tools or { }));

  # `bolt` in a writable copy of src. Pass `bolt` to use that derivation.
  # Otherwise bolt is built from `[tools.bolt]` in the lock.
  # `lock` and `bendLib` match mkProofs: an explicit `bendLib` is BEND_LIB,
  # else the lock's tree, else no BEND_LIB.
  mkLint = {
    bolt ? null,
    src,
    bend ? defaultBend,
    name ? "lint",
    lock ? null,
    bendLib ? null,
  }:
    let
      boltPkg =
        if bolt != null then bolt
        else toolPackage {
          name = "bolt";
          inherit src bend lock;
          wrapFlags = [ "--gpu" "off" ];
        };
    in
    pkgs.runCommand name
      (withBendLib (bendLibFor bendLib src lock) {
        nativeBuildInputs = [ boltPkg ];
      })
      (copyTree src "bolt");

  # ez's own repo as a fresh clone would have it, with no network: the
  # tracked files of src in a new git repo, the lock's BEND_LIB copied into
  # .ez/lib, then the README's steps. `sh bootstrap.sh` must fetch nothing and
  # leave .ez/lib as nix built it, `bend <bin> -o bin/<name>.bin` must build,
  # and that binary's `lock`, with ez.lock.toml deleted, must write the
  # committed lock back byte for byte. `bendLib` is BEND_LIB as in mkProofs;
  # nativeBuildInputs is the C toolchain `bend -o` uses, as in toolPackage.
  mkFresh = {
    src,
    bend ? defaultBend,
    name ? "fresh",
    bendLib ? null,
    nativeBuildInputs ? [ llvm.clang ],
  }:
    let
      tree = bendLibFor bendLib src null;
      file = builtFile src null;
      bin = "bin/${pkgName src null}.bin";
    in
    if tree == null then
      throw "mkFresh needs src/ez.lock.toml or a bendLib"
    else
      pkgs.runCommand name {
        nativeBuildInputs = [ bend pkgs.git ] ++ nativeBuildInputs;
      } ''
        export HOME=$TMPDIR/home
        mkdir -p "$HOME"
        cp -r ${src} src
        chmod -R u+w src
        cd src
        # a clone: every tracked file, in the index `ez lock` lists roots from
        git init -q
        git add -A
        mkdir -p .ez
        cp -r ${tree} .ez/lib
        chmod -R u+w .ez/lib
        # every manifest already matches, so bootstrap fetches and changes nothing
        sh bootstrap.sh 2> bootstrap.err || { cat bootstrap.err; exit 1; }
        if [ -s bootstrap.err ]; then
          echo "bootstrap.sh fetched, but ${tree} already had every package:"
          cat bootstrap.err
          exit 1
        fi
        diff -r ${tree} .ez/lib
        # the README's build
        mkdir -p bin
        BEND_LIB=$PWD/.ez/lib bend ${lib.escapeShellArg file} -o ${lib.escapeShellArg bin}
        # the lock again, from the committed inputs alone. Every dependency is
        # a git pin whose tree is already under BEND_LIB, so nothing is fetched.
        rm ez.lock.toml
        BEND_LIB=$PWD/.ez/lib ${lib.escapeShellArg "./${bin}"} lock
        cmp ${src}/ez.lock.toml ez.lock.toml || {
          diff -u ${src}/ez.lock.toml ez.lock.toml
          exit 1
        }
        echo ok > $out
      '';

  # CC=bend-cc and BEND_LIB=$PWD/.ez/lib. bend-cc belongs in packages.
  # `src`, when set, puts every locked `[tools.*]` on PATH.
  # extraHook runs after those exports.
  mkShell = { packages, extraHook ? "", src ? null }:
    pkgs.mkShellNoCC {
      packages = packages ++ (if src == null then [ ] else devPackages src);
      shellHook = ''
        export CC=bend-cc
        export BEND_LIB=$PWD/.ez/lib
        ${extraHook}
      '';
    };
}

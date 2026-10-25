{
  # bend comes from bendlang/bend's own flake; this one adds the clang the
  # native lane needs. Nothing else: ez is Bend, and what it shells out to is
  # git and coreutils.
  description = "ez: dependency tracking, lockfile and vendoring tool for Bend 2, written in Bend";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # the commit that packages bend 2.0.38 (the v2.0.38 tag packages 2.0.37)
  inputs.bend = {
    url = "github:bendlang/bend/042e797ebd1cfc060603e2682879909fe86fa8c2";
    inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      forEach = nixpkgs.lib.genAttrs systems;
      outputsFor = system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          bend = inputs.bend.packages.${system}.default;
          ez = import ./nix/lib.nix { inherit pkgs bend; };
          bend-cc = ez.bend-cc;
          libssl = "${pkgs.openssl.out}/lib/libssl${pkgs.stdenv.hostPlatform.extensions.sharedLibrary}";

          # the BEND_LIB tree ez's own ledger asks for, built from the lock with no
          # network in the sandbox beyond the lock's own fixed-output fetches
          bendLib = ez.bendLib ./ez.lock.toml;

          # the `ez` binary, built from ez.toml's entry, the top-level main.bend
          # (the program; its modules are under src/), with everything it shells
          # out to on its PATH. curl is not among them: ezhttp speaks HTTP and
          # HTTPS itself, and what it needs instead is libssl by name (it opens it
          # at run time, and no search path reaches a Nix store path) and a CA
          # bundle, which OpenSSL takes from SSL_CERT_FILE. git stays, because
          # `ez add` vendors a repo.
          ezBin = ez.mkPackage {
            inherit bend;
            src = self;
            version = "1.12.0"; # x-release-please-version
            nativeBuildInputs = [ ez.cc ];
            extraPath = [ pkgs.git pkgs.findutils pkgs.coreutils ];
            wrapEnv = {
              EZ_LIBSSL = libssl;
            };
            defaultWrapEnv = {
              SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
            };
            extraInstall = ''
              makeWrapper $out/bin/ez $out/bin/ezx --add-flags tool --add-flags run
            '';
          };

          # `ez prove`: every PROOF.bend, each passing only on a first line of
          # exactly `ALL PROOFS CHECK`. That is the gate CI runs. The end-to-end
          # tests under `tests/` are not run here: they drive real git daemons, a
          # real `bend --publish` and `nix-build`, and the sandbox has no network,
          # no nix daemon and no ports to give them.
          proofs = ez.mkProofs {
            ez = ezBin;
            src = self;
            name = "ez-proofs";
          };
        in {
          packages = {
            ez = ezBin;
            inherit bend bend-cc bendLib;
            default = ezBin;
          };
          # lib.${system}:
          #   bend-cc                         CC for a shell
          #   cc                              the clang `bend -o` builds with
          #   bendLib ./ez.lock.toml          lock path -> BEND_LIB
          #   rtsFlags bend [ "--gpu" "off" ]  runtime options as that bend's
          #                                   binaries read them (+RTS … -RTS
          #                                   from 2.0.38)
          #   mkPackage { bend, src, wrapFlags?, pname?, version?, entry?, lock?,
          #               wrapEnv?, defaultWrapEnv?, extraPath?, extraInstall? }
          #   mkProofs { ez, src, name?, lock?, bendLib? }
          #   mkLint { src, bolt?, bend?, name?, lock?, bendLib? }
          #   mkFresh { src, bend?, name?, bendLib?, nativeBuildInputs? }
          #   toolPackage { name, src, bend?, lock?, wrapFlags?, ... }
          #   devPackages src
          #   mkShell { packages, extraHook?, src? }
          # mkPackage builds `bin` from ez.toml, otherwise `entry`, otherwise
          # main.bend, and wraps $out/bin/<name> with bend on PATH. Version falls
          # back to 0.1.0. mkProofs and mkLint set BEND_LIB from an explicit
          # bendLib, else from lock (or src/ez.lock.toml), else set none.
          # mkFresh is ez's own fresh-clone check: bootstrap.sh over the lock's
          # BEND_LIB fetches nothing, the README's build builds, and `ez lock`
          # writes the committed ez.lock.toml back byte for byte, all offline.
          # A check, which runs `ez prove`:
          #   checks.${system}.proofs = inputs.ez.lib.${system}.mkProofs {
          #     ez = inputs.ez.packages.${system}.default;
          #     src = self;
          #     name = "…-proofs";
          #   };
          # mkShell sets CC=bend-cc and BEND_LIB=$PWD/.ez/lib; put bend-cc in
          # packages.
          lib = ez;
          apps.default = { type = "app"; program = "${ezBin}/bin/ez"; };
          # `lint` is bolt at the lock's `[tools.bolt]` pin, run with
          # `+RTS --gpu off -RTS` over a copy of the tree, graded by ./bolt.bend.
          # `fresh` is EZ-DOC-3 checked directly: a clone's `ez lock` gives back
          # the committed lock. `named` builds ./nix/tests/named with mkPackage
          # and no network. `added` runs `ez add` and builds from the lock it
          # wrote, with no `ez lock` between.
          # `fresh` waits for `ez`: each compile of ez peaks near 3.3 GB, and the
          # two side by side ran a CI runner out of memory.
          checks = {
            inherit proofs;
            lint = ez.mkLint { src = self; };
            fresh = ez.mkFresh { src = self; after = [ ezBin ]; };
            ez = ezBin;
            # bend-lib.nix lays the lock's `[names]`, so a dependency that imports
            # another package by its hub name builds in the sandbox
            named = import ./nix/tests/named.nix {
              inherit pkgs bend;
              nativeBuildInputs = [ ez.cc ];
            };
            # `ez add` writes the lock (EZ-DOC-6): an add on a project that already
            # imports the package, then mkPackage from that lock with no network
            added = import ./nix/tests/added.nix {
              inherit pkgs bend;
              ez = ezBin;
              nativeBuildInputs = [ ez.cc ];
            };
          };
          # `ez` is this tree's build, so `nix develop -c ez lock --upgrade`
          # runs here as it does in a project that depends on ez.
          devShells.default = ez.mkShell {
            src = self;
            packages = [ ezBin bend bend-cc pkgs.git pkgs.openssl pkgs.cacert ];
            # EZ_LIBSSL and SSL_CERT_FILE are what ezhttp's client needs: it
            # opens libssl by name at run time, and OpenSSL takes its trust store
            # from SSL_CERT_FILE.
            extraHook = ''
              export EZ_LIBSSL=${libssl}
              export SSL_CERT_FILE=''${SSL_CERT_FILE:-${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt}
            '';
          };
        };
      perSystem = forEach outputsFor;
      each = name: forEach (system: perSystem.${system}.${name});
    in {
      packages = each "packages";
      lib = each "lib";
      apps = each "apps";
      checks = each "checks";
      devShells = each "devShells";
    };
}

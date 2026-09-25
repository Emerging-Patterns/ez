{
  # bend comes from bendlang/bend's own flake; this one adds the clang the
  # native lane needs. Nothing else: ez is Bend, and what it shells out to is
  # git and coreutils.
  description = "ez: dependency tracking, lockfile and vendoring tool for Bend 2, written in Bend";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  inputs.bend = {
    url = "github:bendlang/bend";
    inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = { self, nixpkgs, ... }@inputs:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      llvm = pkgs.llvmPackages_19;
      bend = inputs.bend.packages.${system}.default;
      ez = import ./nix/lib.nix { inherit pkgs bend; };
      bend-cc = ez.bend-cc;

      # the BEND_LIB tree ez's own ledger asks for, built from the lock with no
      # network in the sandbox beyond the lock's own fixed-output fetches
      bendLib = ez.bendLib ./ez.lock.toml;

      # the `ez` binary, with everything it shells out to on its PATH. curl is
      # not among them: ezhttp speaks HTTP and HTTPS itself, and what it needs
      # instead is libssl by name (it opens it at run time, and no search path
      # reaches a Nix store path) and a CA bundle, which OpenSSL takes from
      # SSL_CERT_FILE. git stays, because `ez add` vendors a repo.
      ezBin = ez.mkPackage {
        inherit bend;
        src = self;
        version = "1.1.0"; # x-release-please-version
        nativeBuildInputs = [ llvm.clang ];
        extraPath = [ pkgs.git pkgs.findutils pkgs.coreutils ];
        wrapEnv = {
          EZ_LIBSSL = "${pkgs.openssl.out}/lib/libssl.so";
        };
        defaultWrapEnv = {
          SSL_CERT_FILE = "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt";
        };
        extraInstall = ''
          makeWrapper $out/bin/ez $out/bin/ezx --add-flags tool --add-flags run
        '';
      };

      # `ez prove`: every PROOF.bend, each passing only on a first line of
      # exactly `All terms check.` That is the gate CI runs. The end-to-end
      # tests under `tests/` are not run here: they drive real git daemons, a
      # real `bend --publish` and `nix-build`, and the sandbox has no network,
      # no nix daemon and no ports to give them.
      proofs = ez.mkProofs {
        ez = ezBin;
        src = self;
        name = "ez-proofs";
      };
    in {
      packages.${system} = {
        ez = ezBin;
        inherit bend bend-cc bendLib;
        default = ezBin;
      };
      # lib.${system}:
      #   bend-cc
      #   bendLib ./ez.lock.toml          lock path -> BEND_LIB
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
      lib.${system} = ez;
      apps.${system}.default = { type = "app"; program = "${ezBin}/bin/ez"; };
      # `lint` is bolt at the lock's `[tools.bolt]` pin, run with `--gpu off`
      # over a copy of the tree, graded by ./bolt.bend. `fresh` is EZ-DOC-3
      # checked directly: a clone's `ez lock` gives back the committed lock.
      # `fresh` waits for `ez`: each compile of ez peaks near 3.3 GB, and the
      # two side by side ran a CI runner out of memory.
      checks.${system} = {
        inherit proofs;
        lint = ez.mkLint { src = self; };
        fresh = ez.mkFresh { src = self; after = [ ezBin ]; };
        ez = ezBin;
      };
      devShells.${system}.default = ez.mkShell {
        src = self;
        packages = [ bend bend-cc pkgs.git pkgs.openssl pkgs.cacert ];
        # EZ_LIBSSL and SSL_CERT_FILE are what ezhttp's client needs: it
        # opens libssl by name at run time, and OpenSSL takes its trust store
        # from SSL_CERT_FILE.
        extraHook = ''
          export EZ_LIBSSL=${pkgs.openssl.out}/lib/libssl.so
          export SSL_CERT_FILE=''${SSL_CERT_FILE:-${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt}
        '';
      };
    };
}

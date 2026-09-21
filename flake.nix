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
      ep = pkgs.callPackage ./nix/lib.nix { };
      bend-cc = ep.bend-cc;

      # the BEND_LIB tree ez's own ledger asks for, built from the lock with no
      # network in the sandbox beyond the lock's own fixed-output fetches
      bendLib = ep.bendLib ./ez.lock.toml;

      # the `ez` binary, with everything it shells out to on its PATH. curl is
      # not among them: net/ speaks HTTP and HTTPS itself, and what it needs
      # instead is libssl by name (it opens it at run time, and no search path
      # reaches a Nix store path) and a CA bundle, which OpenSSL takes from
      # SSL_CERT_FILE. git stays, because `ez add` vendors a repo.
      ez = ep.mkPackage {
        inherit bend;
        src = self;
        version = "0.1.0";
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

      # `--unit-only` leaves out the top-level `tests/`, which drive real git
      # daemons, a real `bend --publish` and `nix-build` — no network, no nix
      # daemon and no ports here. `--js-only` leaves out the native lane: that
      # clang reaches for the system's `ld` and dynamic linker, and a sandbox
      # has neither.
      tests = ep.mkProofs {
        inherit ez;
        src = self;
        name = "ez-tests";
        extraFlags = [ "--js-only" "--unit-only" ];
      };
    in {
      packages.${system} = { inherit ez bend bend-cc bendLib; default = ez; };
      # lib.${system}:
      #   bend-cc
      #   bendLib ./ez.lock.toml          lock path -> BEND_LIB
      #   mkPackage { bend, src, wrapFlags?, pname?, version?, entry?, lock?,
      #               wrapEnv?, defaultWrapEnv?, extraPath?, extraInstall? }
      #   mkProofs { ez, src, name?, extraFlags?, deadline? }
      #   mkLint { bolt, src, name? }
      #   mkShell { packages, extraHook? }
      # mkPackage builds `bin` from ez.toml, otherwise `entry`, otherwise
      # main.bend, and wraps $out/bin/<name> with bend on PATH. Version falls
      # back to 0.1.0. mkProofs and mkLint set BEND_LIB from src/ez.lock.toml
      # when that file is present. mkShell sets CC=bend-cc and
      # BEND_LIB=$PWD/.ez/lib; put bend-cc in packages.
      lib.${system} = ep;
      apps.${system}.default = { type = "app"; program = "${ez}/bin/ez"; };
      checks.${system} = { inherit tests ez; };
      devShells.${system}.default = ep.mkShell {
        packages = [ bend bend-cc pkgs.git pkgs.openssl pkgs.cacert ];
        # EZ_LIBSSL and SSL_CERT_FILE are what the client in net/ needs: it
        # opens libssl by name at run time, and OpenSSL takes its trust store
        # from SSL_CERT_FILE.
        extraHook = ''
          export EZ_LIBSSL=${pkgs.openssl.out}/lib/libssl.so
          export SSL_CERT_FILE=''${SSL_CERT_FILE:-${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt}
        '';
      };
    };
}

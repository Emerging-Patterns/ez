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

      # bend's generated C wants a clang whose ld and dynamic linker are the
      # system's, so a GPU build can still load the system libstdc++
      bend-cc = pkgs.writeShellScriptBin "bend-cc" ''
        exec ${llvm.clang-unwrapped}/bin/clang \
          -resource-dir ${llvm.clang}/resource-root \
          --ld-path=/usr/bin/ld \
          -Wl,--dynamic-linker=/lib64/ld-linux-x86-64.so.2 "$@"
      '';

      # the BEND_LIB tree ez's own ledger asks for, built from the lock with no
      # network in the sandbox beyond the lock's own fixed-output fetches
      bendLib = pkgs.callPackage ./nix/bend-lib.nix { } ./ez.lock.toml;

      # the `ez` binary, with everything it shells out to on its PATH. curl is
      # not among them any more: net/ speaks HTTP and HTTPS itself, and what it
      # needs instead is libssl by name (it opens it at run time, and no search
      # path reaches a Nix store path) and a CA bundle, which OpenSSL takes
      # from SSL_CERT_FILE. git stays, because `ez add` vendors a repo.
      ez = pkgs.stdenv.mkDerivation {
        pname = "ez";
        version = "0.1.0";
        src = self;
        nativeBuildInputs = [ bend llvm.clang pkgs.makeWrapper ];
        BEND_LIB = bendLib;
        buildPhase = "bend ez/main.bend -o ez.bin";
        installPhase = ''
          mkdir -p $out/libexec/ez/bin $out/bin
          cp ez.bin $out/libexec/ez/bin/ez.bin
          makeWrapper $out/libexec/ez/bin/ez.bin $out/bin/ez \
            --set EZ_LIBSSL ${pkgs.openssl.out}/lib/libssl.so \
            --set-default SSL_CERT_FILE ${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt \
            --prefix PATH : ${pkgs.lib.makeBinPath [
              bend pkgs.git pkgs.findutils pkgs.coreutils
            ]}
          makeWrapper $out/bin/ez $out/bin/ezx --add-flags tool --add-flags run
        '';
      };

      # the gate, run by the gate's own runner. This used to be a shell loop
      # that started one `bend` per test file and filtered the check report out
      # of each one with awk. Everything that loop did, `ez test` does better
      # and in Bend: it compiles a project's tests as one program rather than
      # one each, it caches a lane that has already held, it checks every
      # `PROOF.bend` in the tree, and `ez/quiet.bend` is the filter awk was.
      # The loop was kept on the belief that a check could not call `ez`
      # because it would need a built one; the `ez` package two definitions up
      # is a built one, so it can.
      #
      # `--unit-only` is the one thing a sandbox has to say. It leaves out the
      # top-level `tests/`, which drive real git daemons, a real
      # `bend --publish` and `nix-build` — no network, no nix daemon and no
      # ports here. The old loop excluded them by the shape of its glob; this
      # excludes them by asking for it, and for the same reason.
      #
      # `--js-only` is the second. The native lane compiles through a clang
      # that reaches for the system's `ld` and dynamic linker, and a sandbox
      # has neither; the old loop only ever ran the JS lane either.
      #
      # The source is copied because `ez test` writes: `.ez/` holds the shadow
      # it compiles the aggregates in, the cache and each run's output, and the
      # store path it comes from is read-only. `EZ_DEADLINE=0` turns off the
      # five minute budget, which is a number for a developer's machine and not
      # for a builder of unknown speed with a cold cache. procps is for the
      # test that asks which program a started pid turned out to be; the rest
      # of what the runner shells out to rides on the `ez` wrapper's own PATH.
      tests = pkgs.runCommand "ez-tests"
        {
          nativeBuildInputs = [ ez pkgs.procps ];
          BEND_LIB = bendLib;
          EZ_DEADLINE = "0";
        }
        ''
          cp -r ${self} src
          chmod -R u+w src
          cd src
          ez test --js-only --unit-only
          echo ok > $out
        '';
    in {
      packages.${system} = { inherit ez bend bend-cc bendLib; default = ez; };
      # what another project's flake needs from this one: its own lock turned
      # into a BEND_LIB store path. `bendLib` above is this applied to ez's own
      # lock, which is no use to anyone else.
      lib.${system}.bendLib = lock: pkgs.callPackage ./nix/bend-lib.nix { } lock;
      apps.${system}.default = { type = "app"; program = "${ez}/bin/ez"; };
      checks.${system} = { inherit tests ez; };
      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = [ bend bend-cc pkgs.git pkgs.openssl pkgs.cacert ];
        # vendored packages live with the project, not in ~/.bend/lib, so the
        # pin is per project. EZ_LIBSSL and SSL_CERT_FILE are what the client
        # in net/ needs: it opens libssl by name at run time, and OpenSSL takes
        # its trust store from SSL_CERT_FILE.
        shellHook = ''
          export CC=bend-cc
          export BEND_LIB=$PWD/.ez/lib
          export EZ_LIBSSL=${pkgs.openssl.out}/lib/libssl.so
          export SSL_CERT_FILE=''${SSL_CERT_FILE:-${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt}
        '';
      };
    };
}

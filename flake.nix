{
  # bend comes from bendlang/bend's own flake; this one adds bun for the tools
  # that are not ported yet, and the clang the native lane needs.
  description = "ez: dependency tracking and nix builds for Bend 2";

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
      # The TypeScript helpers live beside it under libexec until they are
      # Bend, and EZ_ROOT is how the binary finds them.
      ez = pkgs.stdenv.mkDerivation {
        pname = "ez";
        version = "0.1.0";
        src = self;
        nativeBuildInputs = [ bend llvm.clang pkgs.makeWrapper ];
        BEND_LIB = bendLib;
        buildPhase = "bend ez/main.bend -o ez.bin";
        # the same layout as the repo, since the script finds the binary and the
        # helpers relative to its own parent
        installPhase = ''
          mkdir -p $out/libexec/ez/bin $out/libexec/ez/ez $out/bin
          cp ez.bin $out/libexec/ez/bin/ez.bin
          cp bin/*.ts bin/*.awk $out/libexec/ez/bin/
          cp ez/ez $out/libexec/ez/ez/ez
          makeWrapper $out/libexec/ez/ez/ez $out/bin/ez \
            --set EZ_LIBSSL ${pkgs.openssl.out}/lib/libssl.so \
            --set-default SSL_CERT_FILE ${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt \
            --prefix PATH : ${pkgs.lib.makeBinPath [
              bend pkgs.bun pkgs.git pkgs.findutils pkgs.coreutils
            ]}
        '';
      };

      # every .bend test prints the `#|` lines of its trailer, on the JS lane.
      # git and coreutils are here because run/run.bend runs programs, and a
      # checkout is git's job. curl is gone: net/ speaks HTTP and HTTPS itself,
      # and no test in this set opens a socket, so the sandbox needs no network.
      tests = pkgs.runCommand "ez-tests"
        {
          nativeBuildInputs = [ bend pkgs.git pkgs.coreutils ];
          BEND_LIB = bendLib;
        }
        ''
          cd ${self}
          fail=0
          for t in */tests/*.bend; do
            want=$(sed -n 's/^#|//p' "$t")
            got=$(bend "$t" 2>&1 | awk -f ${self}/bin/quiet.awk)
            if [ "$want" != "$got" ]; then
              echo "FAIL: $t"; diff <(echo "$want") <(echo "$got") | sed 's/^/  /'; fail=1
            fi
          done
          [ $fail = 0 ] || exit 1
          echo ok > $out
        '';
    in {
      packages.${system} = { inherit ez bend bend-cc bendLib; default = ez; };
      apps.${system}.default = { type = "app"; program = "${ez}/bin/ez"; };
      checks.${system} = { inherit tests ez; };
      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = [ bend bend-cc pkgs.bun pkgs.git pkgs.openssl pkgs.cacert ];
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

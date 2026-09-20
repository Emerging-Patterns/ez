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
      bendLib = pkgs.callPackage ./nix/bend-lib.nix { } ./ez.lock.json;

      # the `ez` binary, with everything it shells out to on its PATH. The
      # TypeScript helpers live beside it under libexec until they are Bend,
      # and EZ_ROOT is how the binary finds them: `IO.args()` carries no
      # argv[0], so a binary cannot locate itself.
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
          cp bin/*.ts bin/*.awk $out/libexec/ez/bin/
          makeWrapper $out/libexec/ez/bin/ez.bin $out/bin/ez \
            --set EZ_ROOT $out/libexec/ez \
            --prefix PATH : ${pkgs.lib.makeBinPath [
              bend pkgs.bun pkgs.git pkgs.curl pkgs.findutils pkgs.coreutils
            ]}
        '';
      };

      # every unit test prints the `#|` lines of its trailer, on the JS lane.
      # The glob is `*/tests/*.bend` and so reaches none of the end-to-end
      # tests in the top-level `tests/`: those drive real git daemons, a real
      # `bend --publish` and `nix-build`, none of which a sandbox can do.
      # curl and coreutils are here because run/run.bend runs programs: bend
      # links only pthread and libm, so TLS is curl's job. procps is for the
      # test that asks which program a started pid turned out to be.
      tests = pkgs.runCommand "ez-tests"
        {
          nativeBuildInputs = [ bend pkgs.curl pkgs.coreutils pkgs.procps ];
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
        packages = [ bend bend-cc pkgs.bun pkgs.git pkgs.curl ];
        # vendored packages live with the project, not in ~/.bend/lib, so the
        # pin is per project
        shellHook = ''
          export CC=bend-cc
          export BEND_LIB=$PWD/.ez/lib
        '';
      };
    };
}

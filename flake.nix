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

      # the tools, until they are Bend: bun on PATH, sources beside it
      ez = pkgs.stdenv.mkDerivation {
        pname = "ez";
        version = "0.1.0";
        src = self;
        nativeBuildInputs = [ pkgs.makeWrapper ];
        installPhase = ''
          mkdir -p $out/libexec/ez $out/bin
          cp -r bin $out/libexec/ez/bin
          for t in ez-lock ez-git; do
            makeWrapper ${pkgs.bun}/bin/bun $out/bin/$t \
              --add-flags $out/libexec/ez/bin/$t.ts \
              --prefix PATH : ${pkgs.lib.makeBinPath [ pkgs.git pkgs.nix ]}
          done
        '';
      };

      # every .bend test prints the `#|` lines of its trailer, on the JS lane
      tests = pkgs.runCommand "ez-tests"
        { nativeBuildInputs = [ bend ]; BEND_LIB = bendLib; }
        ''
          cd ${self}
          fail=0
          for t in */tests/*.bend; do
            want=$(sed -n 's/^#|//p' "$t")
            got=$(bend "$t" 2>&1 | grep -v '^All terms check, with [0-9]* unsafe annotation')
            if [ "$want" != "$got" ]; then
              echo "FAIL: $t"; diff <(echo "$want") <(echo "$got") | sed 's/^/  /'; fail=1
            fi
          done
          [ $fail = 0 ] || exit 1
          echo ok > $out
        '';
    in {
      packages.${system} = { inherit ez bend bend-cc bendLib; default = ez; };
      apps.${system}.default = { type = "app"; program = "${ez}/bin/ez-lock"; };
      checks.${system} = { inherit tests ez; };
      devShells.${system}.default = pkgs.mkShellNoCC {
        packages = [ bend bend-cc pkgs.bun pkgs.git ];
        # vendored packages live with the project, not in ~/.bend/lib, so the
        # pin is per project
        shellHook = ''
          export CC=bend-cc
          export BEND_LIB=$PWD/.ez/lib
        '';
      };
    };
}

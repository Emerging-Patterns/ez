# ez

Dependency tracking and Nix builds for [Bend 2](https://github.com/bendlang/bend).

Bend 2 is already a package manager: `bend f.bend --publish` hashes a file and
its local imports into a `0x<hash>` and serves them from a hub, and
`import 0x<hash>/f.bend as P` fetches and checks them. ez adds the three things
that leaves out.

**A ledger.** An import line carries a bare hash and nothing else. `ez.toml`
records what each one is, where it came from, and what a human asked for.

**Nix.** `bend` resolves hub imports during the check, by fetching, which a
sandbox cannot do. ez resolves the graph ahead of time into `ez.lock.toml`, and
`nix/bend-lib.nix` turns that into a `BEND_LIB` store path of fixed-output
derivations.

**Repos that never published.** The `0x` hash is a pure function of the file
set, so ez computes the hash a repo *would* get and vendors it under that name.
The import line is the one a published package would have given you, so if
upstream publishes that tree later the hub simply starts serving it.

## Install

With nix:

```bash
nix profile install github:Emerging-Patterns/ez
```

Without nix — install Bend, then build ez with it:

```bash
curl -fsSL https://bend-lang.com/install.sh | sh
git clone https://github.com/Emerging-Patterns/ez
cd ez
BEND_LIB=$PWD/.ez/lib bend ez/main.bend -o bin/ez.bin
```

Nothing is fetched: the one package ez builds itself with is vendored, and
`bend` only needs telling where it is, since it looks in `~/.bend/lib`
otherwise. Put `bin/ez.bin` on your PATH as `ez`.

`ez add` is the one subcommand with further requirements. It still shells out
to `bin/ez-git.ts`, so it wants `bun`, and `EZ_ROOT` pointing at the checkout
so the binary can find that file wherever you ran it from. Every other
subcommand needs only `bend` and `git`. The nix package sets `EZ_ROOT` for you.

`nix develop` gives a shell with bend, git, openssl and `BEND_LIB` already set.

## Usage

```
ez init [name] [entry.bend]      write an ez.toml for a new project
ez add <url> <ref> <entry.bend>  vendor a git package and record it
ez remove <name>                 drop a package from the ledger
ez lock                          resolve every import, write ez.lock.toml
ez fetch                         fill BEND_LIB from the lock
ez check                         check the entry, without running it
ez build [out]                   build the entry to a native binary
ez run [args..]                  check and run the entry
ez test [--js-only]              run every */tests/*.bend, on both lanes
ez doctor                        report on the toolchain and the project
```

A ledger, and a dependency vendored from a repo that never published:

```toml
[package]
name = "myapp"
entry = "src/main.bend"

[deps.wire]
hash = "0x7e63a5b990a375c304ed462c071214a6"
git = "https://github.com/owner/repo"
rev = "16773c0aa9914b5f04d062469d50100111eb9c9c"
tag = "v1.0"
entry = "src/lib.bend"
```

A dependency with no `git` key lives on the hub. `ez doctor` reports when the
ledger and the repo's import lines disagree; it never rewrites your source.

In a flake:

```nix
bendLib = pkgs.callPackage ./nix/bend-lib.nix { } ./ez.lock.toml;
# ... buildPhase = "BEND_LIB=${bendLib} bend main.bend -o app";
```

`ez test` is the gate: `EZ_PROGRESS=1` to see it work, `EZ_CAP` to change the
memory cap each `bend` runs under.

MIT.

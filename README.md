# ez

Dependency tracking, lockfile and vendoring tool for [Bend 2](https://github.com/bendlang/bend), written in Bend.

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

Install Bend, then build ez with it:

```bash
curl -fsSL https://bend-lang.com/install.sh | sh
git clone https://github.com/Emerging-Patterns/ez
cd ez
BEND_LIB=$PWD/.ez/lib bend ez/main.bend -o bin/ez.bin
```

Nothing is fetched: the packages ez builds itself with are vendored, and
`bend` only needs telling where they are, since it looks in `~/.bend/lib`
otherwise. Put `bin/ez.bin` on your PATH as `ez`.

ez is Bend and nothing else, so the binary is all there is: no runtime, no
helper scripts beside it, nothing to point an environment variable at. Every
subcommand needs `bend` and `git`, and `ez add` also wants `nix` on PATH,
because the NAR hash it records for a vendored repo is `nix hash path`'s to
give.

Or with nix:

```bash
nix profile install github:Emerging-Patterns/ez
```

`nix develop` gives a shell with bend, git, openssl and `BEND_LIB` already set.

## Usage

```
ez init [name] [entry.bend]      scaffold a project: ez.toml, .gitignore, entry
ez add <url> <ref> <entry.bend>  vendor a git package and record it
ez remove <name>                 drop a package from the ledger
ez lock                          resolve every import, write ez.lock.toml
ez fetch                         fill BEND_LIB from the lock
ez check                         check the entry, without running it
ez build [out]                   build the entry to a native binary
ez run [args..]                  check and run the entry
ez publish                       send the entry to the hub, under ez's 0x name
ez test [--js-only] [--full] [--unit-only]
                                 run every */tests/*.bend, on both lanes
ez doctor                        report on the toolchain and the project
```

`ez help` prints that list, and `ez help test` the flags of one command. The
Bend runtime keeps `--help` for itself.

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
root = "."
narHash = "sha256-..."
entry = "src/lib.bend"
```

A dependency with no `git` key lives on the hub. `ez doctor` reports when the
ledger and the repo's import lines disagree; it never rewrites your source.

The ledger is enough on its own. `root` and `narHash` are there so that
`ez lock` never has to consult anything a clone does not have, which is what
lets someone who has just cloned your repo run `ez lock` and get your lock
back to the byte, without re-running `ez add`.

In a flake — ez's own flake turns your lock into a `BEND_LIB` store path, so
there is nothing to copy into your repo:

```nix
inputs.ez.url = "github:Emerging-Patterns/ez";

# ...
bendLib = inputs.ez.lib.${system}.bendLib ./ez.lock.toml;
# ... buildPhase = "BEND_LIB=${bendLib} bend main.bend -o app";
```

Every file comes from a fixed-output derivation keyed by the sha256 the lock
already records, so the build needs no network and `bend` never reaches the hub.

`ez test` is the gate. It compiles a project's tests into one binary rather
than one each, runs every project, end-to-end test and proof at once rather
than in turn, and caches a lane on the content of everything it reads, so a
second run of an unchanged tree is seconds. A whole run has five minutes to
finish in, and one that takes longer fails on that the way a test that printed
the wrong line fails.

`--full` ignores the cache and `EZ_PROGRESS=1` shows the run being planned.
`EZ_CAP` sets the memory cap each `bend` runs under, `EZ_JOBS` how many run at
once, and `EZ_DEADLINE` the budget in seconds, or `0` for no budget. `EZ_JOBS`
defaults to your cores, and never to more of them than the memory cap divides
the machine into, since any one `bend` may claim the whole cap.

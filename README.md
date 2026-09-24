# ez

ez: project management for bend

**ez** is a project manager for [Bend](https://github.com/bendlang/bend). Bend
is already a package manager: `bend … --publish` hashes a file and its local
imports into a `0x…` and serves them from a hub, and `import 0x…` fetches and
checks them. ez sits on top of that: init, deps, lock, build, run, and install
tools for a whole project.

## Install

Install Bend, then fetch the packages ez builds itself with, and build it:

```bash
curl -fsSL https://bend-lang.com/install.sh | sh
git clone https://github.com/Emerging-Patterns/ez
cd ez
sh bootstrap.sh
mkdir -p bin
BEND_LIB=$PWD/.ez/lib bend ez/main.bend -o bin/ez.bin
```

ez runs on Bend 2.0.27, the version CI builds with. Its dependencies are
pinned to git revs, and `ez fetch` is what fetches them, which ez cannot run
before it is built. `bootstrap.sh` is that one step, and the one helper script
in the repo: it reads `ez.lock.toml`, fetches each package at its pinned rev
into `.ez/lib`, and checks every file's sha256 and the package's `0x` name
against the lock. It needs `git` and `sha256sum` (or `shasum`), and nothing
comes from the hub. `bend` then only needs telling where the packages are,
since it looks in `~/.bend/lib` otherwise.

Put `bin/ez.bin` on your PATH as `ez`. ez is Bend and nothing else, so the
binary is all there is: no runtime, no helper scripts beside it, nothing to
point an environment variable at. Every subcommand needs `bend` and `git` on
PATH. `ezx` is `ez tool run`; to have one, put this next to that `ez`:

```sh
printf '%s\n' '#!/bin/sh' 'exec ez tool run "$@"' > ezx && chmod +x ezx
```

Or with nix, which needs none of the above:

```bash
nix profile install github:Emerging-Patterns/ez
```

That install provides `ez` and `ezx`. `nix develop` gives a shell with bend,
git, openssl and `BEND_LIB` already set.

## Quickstart

```bash
git init myapp && cd myapp
ez init myapp                    # ez.toml, .gitignore and main.bend
git add -A
ez add Emerging-Patterns/snap    # pin a git package; prints its import line
ez lock                          # write ez.lock.toml
ez run                           # check and run main.bend
```

On a fresh clone of a project, `ez fetch` fills `BEND_LIB` from the lock.

## Usage

```
ez init [name] [entry.bend]      scaffold a project: ez.toml, .gitignore, entry
ez add <target> [ref] [entry.bend] [--rename NAME]
                                 vendor a git package and record it
ez remove <name>                 drop a package from the ledger
ez lock [--upgrade] [--package NAME]
                                 resolve every import, write ez.lock.toml
ez fetch                         fill BEND_LIB from the lock
ez check                         check the entry, without running it
ez build [out]                   build the entry to a native binary
ez run [args..]                  check and run the entry
ez tool sync                      build and link every pinned tool, at its lock rev
ez tool run <target> [-- args..] fetch, build and run a repo's binary
ez tool install <target>         build the binary and link it on PATH
ez tool upgrade <target>         rebuild when the commit moved, refresh the link
ezx <target> [-- args..]         ez tool run, when ezx is on PATH
ez publish                       send the entry to the hub, under ez's 0x name
ez test                          run every */tests/*.bend against its trailer
ez prove                         check every PROOF.bend: the proof gate
ez doctor                        report on the toolchain and the project
```

`ez help` prints that list, and `ez help test` the flags of one command.

The ledger, `ez.toml`, with a dependency vendored from a repo that never
published:

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

In a flake, build the program the ledger names, with `BEND_LIB` made from
`ez.lock.toml`:

```nix
inputs.ez.url = "github:Emerging-Patterns/ez";
pkg = inputs.ez.lib.${system}.mkPackage { inherit bend; src = self; };
```

## More

- [docs/guide.md](docs/guide.md): every command in detail: the ledger and
  naming, lock and upgrade, fetch and vendoring, tools, the hub, publish,
  doctor, nix, and prove and test.
- [SPEC.md](SPEC.md): what ez guarantees, each requirement with the laws that
  prove it.
- [docs/rfc/ez-spec.md](docs/rfc/ez-spec.md): the design, and how ez got
  here.

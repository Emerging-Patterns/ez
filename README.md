# ez

ez: project management for bend

**ez** is a project manager for [Bend](https://github.com/bendlang/bend). Bend
is already a package manager: `bend … --publish` hashes a file and its local
imports into a `0x…` and serves them from a hub, and `import 0x…` fetches and
checks them. ez sits on top of that — init, deps, lock, build, run, and
install tools for a whole project.

## Install

Install Bend, then build ez with it:

```bash
curl -fsSL https://bend-lang.com/install.sh | sh
git clone https://github.com/Emerging-Patterns/ez
cd ez
BEND_LIB=$PWD/.ez/lib bend ez/main.bend -o bin/ez.bin
```

Nothing is fetched: the one package ez builds itself with is vendored, and
`bend` only needs telling where it is, since it looks in `~/.bend/lib`
otherwise. Put `bin/ez.bin` on your PATH as `ez`. The command is
`ez tool run`. To name it `ezx`, put this next to that `ez`:

```sh
printf '%s\n' '#!/bin/sh' 'exec ez tool run "$@"' > ezx && chmod +x ezx
```

ez is Bend and nothing else, so the binary is all there is: no runtime, no
helper scripts beside it, nothing to point an environment variable at. Every
subcommand needs `bend` and `git`, and `ez add` also wants `nix` on PATH,
because the NAR hash it records for a vendored repo is `nix hash path`'s to
give.

Or with nix:

```bash
nix profile install github:Emerging-Patterns/ez
```

That install provides `ez` and `ezx`. `ezx` is `ez tool run`. `nix develop`
gives a shell with bend, git, openssl and `BEND_LIB` already set.

## Usage

```
ez init [name] [entry.bend]      scaffold a project: ez.toml, .gitignore, entry
ez add <target> [ref] [entry.bend]  vendor a git package and record it
ez remove <name>                 drop a package from the ledger
ez lock [--upgrade] [--package NAME]
                                 resolve every import, write ez.lock.toml
ez fetch                         fill BEND_LIB from the lock
ez check                         check the entry, without running it
ez build [out]                   build the entry to a native binary
ez run [args..]                  check and run the entry
ez tool run <target> [-- args..] fetch, build and run a repo's binary
ez tool install <target>         build the binary and link it on PATH
ez tool upgrade <target>         rebuild when the commit moved, refresh the link
ezx <target> [-- args..]         ez tool run, when ezx is on PATH
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
bin = "src/main.bend"

[deps.wire]
hash = "0x7e63a5b990a375c304ed462c071214a6"
git = "https://github.com/owner/repo"
rev = "16773c0aa9914b5f04d062469d50100111eb9c9c"
tag = "v1.0"
root = "."
narHash = "sha256-..."
entry = "src/lib.bend"
```

`bin` is the file `ez tool run`, `ez tool install`, `ez tool upgrade`, and
`ezx` build. With no `bin`, that is the entry. `owner/repo` is
`https://github.com/owner/repo`. A git URL is kept. Any other target is a
path (`/…`, `./…`, `../…`, `~/…`, or a word that is not `owner/repo`). The
checkout and the binary are cached under `$XDG_CACHE_HOME/ez/tool/<slug>`
(`~/.cache/ez/tool/<slug>` when that is unset).

A remote resolves to `git ls-remote <url> HEAD`. A path resolves to a clean
`HEAD`. The checkout is reused while `rev` is that commit, and the binary
is reused while it was built from that commit. A dirty worktree, or a path
that is not a checkout, has no commit and is built every time.

`ez tool install` fetches the lock and builds `<slug>/bin/<name>.out`, then
links that file onto PATH as `<name>`. `<name>` is the package name in the
target's `ez.toml` (`bolt` for bolt), or `app` when the ledger names none.
The link is `$EZ_TOOL_BIN/<name>` when `EZ_TOOL_BIN` is set, otherwise
`$XDG_BIN_HOME/<name>`, otherwise `~/.local/bin/<name>`. The directory is
created when it is missing. `ez tool upgrade` reads that commit again and
rebuilds when it is not the one in `rev`, or when the binary is missing,
and writes that link again. The same commit is left in place. Neither
command runs the binary. `ez tool run` does, and the built program's status
is the status of the command. A target, ledger, fetch, build or link that
fails exits 1.

`ez add` takes the same kind of target. With no ref, it pins the latest
semver-ish tag on the remote. With no such tag, it pins `main`, or `master`
when `main` is absent. With no entry, it reads `[package] entry` from that
revision's `ez.toml`, then `[package] bin` when `entry` is absent, then
`main.bend`. A ref and an entry given on the command line are used as given.

A dependency with no `git` key lives on the hub. `vendor = true` commits that
dependency's tree under `.ez/lib/<hash>` and names the hash in `.gitignore`.
Without it, the tree is not committed: `ez fetch` fills `BEND_LIB` from the
lock. `ez doctor` reports when the ledger and the repo's import lines
disagree; it never rewrites your source.

`ez lock --upgrade` re-pins git dependencies, then writes the lock.
`--package NAME` limits that to one. A `tag` is re-resolved. A dependency
with only a `rev` moves to the default branch tip when the pinned commit is
an ancestor of it, and stays a commit pin. A hub dependency does not move.
The upgrade does not fetch the rest of the lock. A dependency marked
`vendor` is laid out again under the new hash, and the gitignore allowlist
follows it. An import line that names a hash that moved is rewritten to
name the new one.

The ledger is enough on its own. `root` and `narHash` are there so that
`ez lock` never has to consult anything a clone does not have, which is what
lets someone who has just cloned your repo run `ez lock` and get your lock
back to the byte, without re-running `ez add`.

In a flake — `lib.${system}` builds the program the ledger names and turns
`ez.lock.toml` into a `BEND_LIB` store path, so there is nothing to copy
into your repo:

```nix
inputs.ez.url = "github:Emerging-Patterns/ez";

# ...
ez = inputs.ez.lib.${system};
ezBin = inputs.ez.packages.${system}.default;

pkg = ez.mkPackage { inherit bend; src = self; };

proofs = ez.mkProofs { ez = ezBin; src = self; };
lint = ez.mkLint { inherit bolt; src = self; };
```

`mkPackage` builds `bin` from `ez.toml` when that is set, otherwise `entry`,
otherwise `main.bend`, and wraps the binary with `bend` on `PATH`. `BEND_LIB`
comes from `ez.lock.toml`. `ez.bendLib ./ez.lock.toml` is that tree on its
own. Every file comes from a fixed-output derivation keyed by the sha256 the
lock already records, so the build needs no network and `bend` never reaches
the hub.

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

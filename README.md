# ez

ez: project management for bend

**ez** is a project manager for [Bend](https://github.com/bendlang/bend). Bend
is already a package manager: `bend … --publish` hashes a file and its local
imports into a `0x…` and serves them from a hub, and `import 0x…` fetches and
checks them. ez sits on top of that — init, deps, lock, build, run, and
install tools for a whole project.

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

ez's dependencies are pinned to git revs, and `ez fetch` is what fetches
them, which ez cannot run before it is built. `bootstrap.sh` is that one
step, and the one helper script in the repo: it reads `ez.lock.toml`,
fetches each package at its pinned rev into `.ez/lib`, and checks every file's
sha256 and the package's `0x` name against the lock. It needs `git` and
`sha256sum` (or `shasum`), and nothing comes from the hub. `bend` then only
needs telling where the packages are, since it looks in `~/.bend/lib`
otherwise. With nix none of this is needed; see below. Put `bin/ez.bin` on
your PATH as `ez`. The command is `ez tool run`. To name it `ezx`, put this
next to that `ez`:

```sh
printf '%s\n' '#!/bin/sh' 'exec ez tool run "$@"' > ezx && chmod +x ezx
```

ez is Bend and nothing else, so the binary is all there is: no runtime, no
helper scripts beside it, nothing to point an environment variable at. Every
subcommand needs `bend` and `git` on PATH.

Or with nix:

```bash
nix profile install github:Emerging-Patterns/ez
```

That install provides `ez` and `ezx`. `ezx` is `ez tool run`. `nix develop`
gives a shell with bend, git, openssl and `BEND_LIB` already set.

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

`ez help` prints that list, and `ez help test` the flags of one command. The
Bend runtime keeps `--help` for itself.

`ez init` starts a project and never writes over one: in a directory that
already has an `ez.toml` it exits 1 and writes nothing. It is also the only
command that makes a ledger: `ez add`, `ez remove` and `ez lock` (with or
without `--upgrade`) in a directory with no `ez.toml` exit 1 and write
nothing.

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

`[deps.*]` is a package. It is imported, and `ez fetch` puts it on `BEND_LIB`.
A CLI is a `[tools.*]` pin. It is not imported and it is not put on
`BEND_LIB`. `ez lock` records it under `[tools.bolt]` in `ez.lock.toml`,
copying `rev` and `narHash` from the ledger; a pin missing either stops
`ez lock` with exit 1 and the command that fills it,
`ez lock --upgrade --package bolt`. `ez lock --upgrade` fills an empty pin,
re-resolves the tag and fills `narHash`, the way it does for a git
dependency. `ez tool sync` builds and links every such pin at the lock rev.
`ez tool run bolt` uses that rev; `ez tool run owner/repo` is still the
repo's HEAD.

```toml
[tools.bolt]
git = "https://github.com/Emerging-Patterns/bolt"
tag = "v0.4.0"
rev = "24b497e294a08f6a83e0b08ece3795f813421b87"
root = "."
narHash = "sha256-…"
entry = "bolt/main.bend"
```

`bin` is the file `ez tool run`, `ez tool install`, `ez tool upgrade`, and
`ezx` build. With no `bin`, that is the entry. A target with `://` in it,
or starting `git@`, is a git URL and is kept. A target starting `/`, `./`,
`../` or `~/` is a path. `owner/repo` (exactly two segments of letters,
digits, `-`, `_` and `.`, neither of them `.` or `..`) is
`https://github.com/owner/repo` unless the second segment ends in `.bend`, so
`vercel/next.js` is GitHub and `src/main.bend` is a path. Anything else is a
path. The checkout and the binary are cached under
`$XDG_CACHE_HOME/ez/tool/<slug>` (`~/.cache/ez/tool/<slug>` when that is
unset); the slug of a URL or of
`owner/repo` drops a trailing `.git`.

A remote resolves to `git ls-remote <url> HEAD`. A path resolves to a clean
`HEAD`. A name that matches a `[tools.*]` pin resolves to the rev in
`ez.lock.toml`. The checkout is reused while `rev` is that commit. The binary
is reused while `key` names that commit, the same built file and the same
`bend version`, so a pin's `bin` or `entry` and a free run of the same commit
do not share a binary, and a new bend rebuilds it. A dirty worktree, or a path
that is not a checkout, has no commit and is built every time.

`ez tool install` fetches the lock and builds `<slug>/bin/<name>.out`, then
links that file onto PATH as `<name>`. Each long step says what it is doing
before it waits, and on success the command names what it installed and where
the link is. `<name>` is the package name in the
target's `ez.toml` (`bolt` for bolt), or `app` when the ledger names none.
The link is `$EZ_TOOL_BIN/<name>` when `EZ_TOOL_BIN` is set, otherwise
`$XDG_BIN_HOME/<name>`, otherwise `~/.local/bin/<name>`. The directory is
created when it is missing. `ez tool upgrade` reads that commit again and
rebuilds when it is not the one in `rev`, or when the binary is missing,
and writes that link again. The same commit is left in place. Neither
command runs the binary. `ez tool run` does, and the built program's status
is the status of the command. A target, ledger, fetch, build or link that
fails exits 1.

`ez add` takes the same kind of target. A relative path is recorded as it
was given, relative to the project, which is the directory ez runs in, since
every command reads `ez.toml` from there; an absolute one stays absolute.
`ez add`, `ez lock`, `ez fetch` and `ez lock --upgrade` all read a relative
`git` from the project, so a project and a sibling repo moved together still
lock to the same bytes. With no ref, it pins the greatest
semver-ish release tag on the remote (`v1.9.0` beats `v2.0.0-rc1`); with no
release, the greatest pre-release; with no semver-ish tag at all, the
remote's default branch, as its `HEAD` names it. A remote whose `HEAD` names
no branch is refused. A named ref resolves exactly: `refs/tags/<ref>` first,
then `refs/heads/<ref>`, so a tag beats a branch of the same name and `main`
never resolves to `feature/main`. A 40-hex ref is used as the commit without
asking the remote. The tag or branch is recorded as `tag`, which
`ez lock --upgrade` re-resolves. With no entry, it reads `[package] entry`
from that revision's `ez.toml`, then `[package] bin` when `entry` is absent,
then `main.bend`. An entry given on the command line is used as given.
An entry the revision does not hold is refused, and so is a package whose
imports climb out of the checkout. The package is walked from the files of
the checkout itself, so its hash, the files laid under `BEND_LIB` and their
manifest all come from one reading of it.
The dependency is named the way cargo names one, never after its entry.
`--rename NAME`, like `cargo add --rename`, records it under `NAME` ahead of
every rule below; `NAME` must be a TOML bare key, and a source the ledger
already records under another name is refused rather than recorded twice.
Otherwise a source the ledger already records keeps the name it has there,
so adding it again replaces that entry. Otherwise a target that is an ez
project is named by the `[package] name` of its ez.toml at the fetched rev,
when that is a TOML bare key (letters, digits, `-`, `_`); a name that is not one falls
through rather than being refused. Otherwise `owner/repo` or a URL is named
by the repository (`[deps.repo]`, any `.git` dropped), and a path by its
directory. A name the ledger gives to another source stops `ez add` with
exit 1 and leaves the ledger as it was, `--rename` included; remove that
entry, or add this one with `--rename` under another name. Whatever stops
it, `ez add` writes nothing: not the ledger, not `.gitignore`, and no tree,
not even in `BEND_LIB`. With no ledger, one that does not parse, a target
that names nothing, or a `--rename` refused by the ledger alone, it stops
before asking the remote anything.

A dependency with no `git` key lives on the hub. `vendor = true` commits that
dependency's tree under `.ez/lib/<hash>` and names the hash in `.gitignore`.
`ez add` records a new dependency without it; you set it by hand, and
adding the dependency again keeps it, lays the new tree under
`.ez/lib/<hash>` rather than `BEND_LIB`, and removes the old committed tree
when the hash moved and no other dependency names it. The allowlist is derived from the
ledger: after `ez add`, `ez remove` or `ez lock --upgrade`, the
`!.ez/lib/<hash>` lines of `.gitignore` are exactly the hashes of the
dependencies marked `vendor = true`, each once, in the order the ledger
first names them, and every other line is left as it was, blank lines
included. A missing hash is written where the first allowlist
line was, or at the end of the file; a hash the ledger no longer vendors is
dropped. ez counts as its own any `!` line under `.ez/lib/`, however it
is spelled (a leading or trailing `/`, surrounding blanks), and writes the
ones it keeps as `!.ez/lib/<hash>`. The allowlist
needs `.ez/*`, `!.ez/lib` and `.ez/lib/*`, which `ez init` writes: git
cannot re-include a file under a directory it has excluded, so under a bare
`.ez/` no allowlist line works, and ez replaces that line with the three.
The file is only written when this changes it.
`ez remove <name>` drops the dependency from the ledger and the allowlist
with it. A vendored dependency's committed tree, `.ez/lib/<hash>`, is
removed too, unless another dependency still names that hash. A name the
ledger does not have stops `ez remove` with exit 1, and it writes nothing,
as `cargo remove` does.
Without `vendor = true`, the tree is not committed: `ez fetch` fills `BEND_LIB` from the
lock, checking every file against the lock's sum and every package against
its name before it lays anything, and refuses with exit 1, writing nothing,
when there is no ez.toml or no lock, as `uv sync --frozen` does. `ez lock` fetches a git dependency whose tree is not under
`BEND_LIB` at the ledger's `rev`, checks it against `narHash`, and leaves it
there once the lock is written. A fetch or a check that fails stops the lock
with exit 1, and a lock that stops writes nothing: not the lock, and no tree. `ez doctor`
reports when the ledger and the repo's import lines disagree; it never
rewrites your source.

Hub packages come from `https://hub.bend-lang.com`, or from the hub a `hub`
key in the ledger's `[package]` table names. `ez lock` does not read
`BEND_HUB`.

`ez lock --upgrade` re-pins git dependencies and `[tools.*]` pins, then
writes the lock. `--package NAME` limits that to one dependency or one tool.
A `tag` is re-resolved. A dependency
with only a `rev` moves to the default branch tip when the pinned commit is
an ancestor of it, and stays a commit pin. A hub dependency does not move.
The upgrade itself fetches only the dependencies it re-pins; the lock it
then writes fetches any other git dependency whose tree is missing, the way
a plain `ez lock` does. A pinned commit whose tree no longer weighs to the
pin is a drift, and stops the upgrade. A dependency marked
`vendor` is laid out again under `.ez/lib/<new hash>`, its old tree is
removed, and the gitignore allowlist follows it; any other moved tree is
left under `BEND_LIB`. An import line that starts `import <old>/`, at
column 0, is rewritten to start `import <new>/`, and no other line changes. The upgrade and the lock are one plan: ez.toml is
written once, then `.gitignore`, the rewritten sources and the lock, and an
upgrade that stops, or a lock after it that stops, writes nothing at all. It
does not write `.ez/origins.toml`.

The ledger is enough on its own. `ez lock` reads the ledger, the `.bend`
files `git ls-files` lists (so it refuses outside a git repository), the
committed trees under `.ez/lib`, each git dependency's files at its ledger
`rev`, and hub content. It takes the hub imports of every listed file and
follows no local import, so an untracked file never reaches the lock, even
one a tracked file imports. Every package is checked against its `0x` name
and every file against its sum, whatever it was read from; a tree already
under `BEND_LIB` is judged as the same bytes cloned at the ledger's `rev`
with the ledger's `narHash`. A lock whose hashes, paths or values would not
read back (a repeated hash, or a `"`, `\` or newline in one) is refused. It
reads no record of origins beside the ledger, and no command writes one:
a hash the ledger does not name is fetched from the hub, and when the hub does not have it the
lock says the ledger does not name it and exits 1. It does not record the
bend that ran it. `root` and `narHash` are there so that `ez lock` never has
to consult anything a clone does not have, which is what lets someone who
has just cloned your repo run `ez lock` and get your lock back to the byte,
without re-running `ez add`.

In a flake — `lib.${system}` builds the program the ledger names and turns
`ez.lock.toml` into a `BEND_LIB` store path, so there is nothing to copy
into your repo:

```nix
inputs.ez.url = "github:Emerging-Patterns/ez";

# ...
ez = inputs.ez.lib.${system};

pkg = ez.mkPackage { inherit bend; src = self; };

checks.${system}.proofs = ez.mkProofs {
  ez = inputs.ez.packages.${system}.default;
  src = self;
  name = "…-proofs";
};
lint = ez.mkLint { src = self; };
```

`mkLint` builds `bolt` from `[tools.bolt]` in the lock. `toolPackage` builds
one locked tool, and `devPackages src` builds every one. `mkShell` puts those
on `PATH` when `src` is set. None of these need `inputs.bolt`.

`mkPackage` builds `bin` from `ez.toml` when that is set, otherwise `entry`,
otherwise `main.bend`, and wraps the binary with `bend` on `PATH`. `lock` is
an explicit lock path. `bendLib`, when set, is the store path used as
`BEND_LIB` and wins over that lock. With neither, `BEND_LIB` comes from
`src/ez.lock.toml` when that file is present. `ez.bendLib ./ez.lock.toml` is
that tree on its own. Every file comes from a fixed-output derivation keyed
by the sha256 the lock already records, so the build needs no network and
`bend` never reaches the hub. `mkProofs` runs `ez prove` over a copy of
`src`, and this repo's own `proofs` check is that. This repo's `fresh` check
(`mkFresh`) is a clone with no network: `sh bootstrap.sh` over that tree
fetches nothing, the build above builds, and `ez lock` with `ez.lock.toml`
deleted writes it back byte for byte. CI also follows the install steps
above without nix and runs `ez prove`.

`ez prove` is the gate. It runs `bend` on every PROOF.bend in the tree, all at
once, and passes a proof only when the first line bend prints is exactly
`All terms check.`: bend exits 0 on a proof that leans on unsafe or foreign
code, so the exit status is not enough. It prints a line for each proof and
then the count, and exits 1 when any proof failed. Nothing is cached, so every
run checks every proof.

`ez test` runs every `*/tests/*.bend`, each as its own `bend`, all at once, and
holds each run's output to the `#|` trailer at the end of its file. This
repo's are the end-to-end tests under `tests/`, which drive real git daemons,
`bend --publish` and `nix-build`, so CI does not run them. A whole run has five
minutes to finish in, and one that takes longer fails on that the way a test
that printed the wrong line fails.

`EZ_CAP` sets the memory cap each `bend` runs under and `EZ_JOBS` how many run
at once, for both commands. `EZ_DEADLINE` is `ez test`'s budget in seconds, or
`0` for no budget. `EZ_JOBS` defaults to your cores, and never to more of them
than the memory cap divides the machine into, since any one `bend` may claim
the whole cap.

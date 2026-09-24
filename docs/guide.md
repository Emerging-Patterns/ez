# The ez guide

This is the reference for ez's commands. The [README](../README.md) has the
install steps and a quickstart; [SPEC.md](../SPEC.md) lists what ez
guarantees, each requirement with the laws that prove it. Requirement IDs
such as (EZ-VEN-1) below point at its rows.

Every subcommand needs `bend` and `git` on PATH. `ez help` prints the command
list, and `ez help test` the flags of one command. The Bend runtime keeps
`--help` for itself.

Every command exits 0 on success and 1 on any failure ez detects, except
`ez run` and `ez tool run`, which exit with the program's status (EZ-OUT-1).
A command that refuses writes nothing (EZ-OUT-2).

- [init](#init)
- [The ledger](#the-ledger)
- [Adding a dependency](#adding-a-dependency)
- [Lock](#lock)
- [Upgrade](#upgrade)
- [Fetch and vendoring](#fetch-and-vendoring)
- [Check, build and run](#check-build-and-run)
- [Tools](#tools)
- [The hub](#the-hub)
- [Publish](#publish)
- [Doctor](#doctor)
- [Nix](#nix)
- [Prove and test](#prove-and-test)

## init

`ez init [name] [entry.bend] [--description TEXT]` scaffolds a project the
way `cargo new` does: `ez.toml`, `.gitignore`, the entry, and a library under
`src/` that the entry imports.

```
$ ez init demo --description "a demo"
$ cat main.bend
# demo: a demo
import Base
import ./src/lib.bend as Lib

def main() -> IO(Unit):
  IO.print(Lib.greeting())
$ ez run
hello
```

- The name defaults to `app` and the entry to `main.bend`.
- The entry opens with `# <name>: <description>`. The hub describes a package
  by the first line of its first file by path, and `main.bend` comes before
  `src/`, so this is the line the hub shows once the package is published
  (see [Publish](#publish)). With no `--description` the line is
  `# <name>: TODO describe <name>`, to be edited before then. A description
  is one line; one holding a newline is refused (EZ-INIT-1).
- `src/lib.bend` is written only with an entry at the project's top, where
  `./src/lib.bend` finds it, and only when nothing is there yet. An entry in
  a directory of its own, such as `ez init app src/main.bend`, is written
  alone (EZ-INIT-2).
- An entry or a `src/lib.bend` that is already there is never written over,
  and neither gets the description then (EZ-INIT-2).
- The layout is a default for new projects, not a rule: any entry the ledger
  names works, and `ez doctor` does not check where files are.
- It never writes over a project. In a directory that already has an
  `ez.toml` it exits 1 and writes nothing.
- It is the only command that makes a ledger. In a directory with no
  `ez.toml`, `ez add`, `ez remove`, `ez fetch` and `ez lock` (with or without
  `--upgrade`) exit 1 and write nothing, and `ez check`, `ez build` and
  `ez run` exit 1 and start nothing (EZ-LED-6).
- It refuses a name or entry that a ledger cannot carry (see below), and a
  description holding a newline, and then writes nothing.

The `.gitignore` it writes holds `.ez/*`, `!.ez/lib` and `.ez/lib/*`, which
the vendoring allowlist needs (see [Fetch and vendoring](#fetch-and-vendoring)).

## The ledger

`ez.toml` is the ledger. A ledger, and a dependency vendored from a repo that
never published:

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

- `[deps.*]` is a package. It is imported, and `ez fetch` puts it on
  `BEND_LIB`.
- A dependency with no `git` key lives on the hub.
- A CLI is a `[tools.*]` pin. It is not imported and not put on `BEND_LIB`
  (see [Tools](#tools)).
- `bin` is the file the tool commands build. With no `bin`, that is the entry.
- `publish-as` and `version` name the package on the hub when it is published
  (see [Publish](#publish)). `ez init` writes neither.
- `root` and `narHash` are there so that `ez lock` never has to consult
  anything a clone does not have (see [Lock](#lock)).

Paths in the ledger use forward slashes, on every system: write
`src/main.bend`, not `src\main.bend`.

The ledger is enough on its own: no command writes or reads a record of
origins beside it (there is no `.ez/origins.toml`).

### What ez will write

`ez init`, `ez add`, `ez remove` and `ez lock --upgrade` write only a ledger
that reads back as what they meant to write (EZ-LED-4). Each refuses, with
exit 1 and nothing written, a ledger where:

- a name or value holds `"`, `\` or a newline;
- a dependency has no hash;
- a git source names no repo or no root.

So `ez init 'my"app'` refuses, and so does `ez remove` on a hand-edited
`entry = "src\main.bend"`. The last two cases cannot come from a ledger ez
read, so they only meet values you typed or edited in.

## Adding a dependency

`ez add <target> [ref] [entry.bend] [--rename NAME]` vendors a git package and
records it in the ledger. On success it prints the import line for the
entry's path inside the package, the line `ez publish` prints (EZ-RES-2).
`ez add <name>@<version> [entry.bend]` records a hub package by its name
instead (see "Named imports" below).

### Targets

`ez add` and the tool commands read a target the same way (EZ-RES-3):

- A target with `://` in it, or starting `git@`, is a git URL and is kept.
- A target starting `/`, `./`, `../` or `~/` is a path.
- `owner/repo`, exactly two segments of letters, digits, `-`, `_` and `.`,
  neither of them `.` or `..`, is `https://github.com/owner/repo`, unless the
  second segment ends in `.bend`. So `vercel/next.js` is GitHub and
  `src/main.bend` is a path.
- Anything else is a path. The empty word is refused.
- For `ez add` only, a path that bend reads as a hub package's
  `<name>@<version>` (a-z, 0-9 and `-`, 12 to 64 characters, then `@` and four
  numbers like `1.0.0.0`) is that package on the hub. A git URL,
  `git@host:path` or `owner/repo` never is.

A relative path is recorded as it was given, relative to the project, which
is the directory ez runs in, since every command reads `ez.toml` from there.
An absolute one stays absolute, and a leading `~/` is expanded. `ez add`,
`ez lock`, `ez fetch` and `ez lock --upgrade` all read a relative `git` from
the project, so a project and a sibling repo moved together still lock to the
same bytes (EZ-LED-8).

### Refs

With no ref, `ez add` pins (EZ-RES-1):

1. the greatest semver-ish release tag on the remote (`v1.9.0` beats
   `v2.0.0-rc1`);
2. with no release, the greatest pre-release;
3. with no semver-ish tag at all, the remote's default branch, as its `HEAD`
   names it. A remote whose `HEAD` names no branch is refused.

A named ref resolves exactly: `refs/tags/<ref>` first, then
`refs/heads/<ref>`. So a tag beats a branch of the same name, and `main`
never resolves to `feature/main`. A 40-hex ref is used as the commit without
asking the remote. The tag or branch is recorded as `tag`, which
`ez lock --upgrade` re-resolves.

### Entry

With no entry, `ez add` reads `[package] entry` from that revision's
`ez.toml`, then `[package] bin` when `entry` is absent, then `main.bend`. An
entry given on the command line is used as given. It refuses:

- an entry the revision does not hold;
- a package whose imports climb out of the checkout;
- a package with a file under a directory named `license`, in any case, as
  bend 2.0.27 does.

The package is walked from the files of the checkout itself, so its hash, the
files laid under `BEND_LIB` and their manifest all come from one reading of
it. Like `bend --publish` in 2.0.27, the walk takes along every file named
exactly `LICENSE` beside a file of the package, and the hash covers it.

A dependency pinned before bend 2.0.27 has a hash that does not cover its
`LICENSE` files. ez keeps that recorded name, as cargo and uv keep a checksum
they recorded: `ez lock` and `ez lock --upgrade` judge such a checkout
without its `LICENSE` files when the full manifest does not match the name.
Only a new `ez add` takes the new rule.

### Naming

The dependency is named the way cargo names one, never after its entry
(EZ-LED-7). The first rule that applies wins:

1. `--rename NAME`, like `cargo add --rename`, records it under `NAME`.
   `NAME` must be a TOML bare key, and a source the ledger already records
   under another name is refused rather than recorded twice.
2. A source the ledger already records keeps the name it has there, so adding
   it again replaces that entry.
3. A target that is an ez project is named by the `[package] name` of its
   `ez.toml` at the fetched rev, when that is a TOML bare key (letters,
   digits, `-`, `_`). A name that is not one falls through rather than being
   refused.
4. `owner/repo` or a URL is named by the repository (`[deps.repo]`, any
   `.git` dropped).
5. A path is named by its directory.

A name the ledger gives to another source stops `ez add` with exit 1 and
leaves the ledger as it was, `--rename` included. Remove that entry, or add
this one with `--rename` under another name.

### What a refused add leaves

Whatever stops it, `ez add` writes nothing: not the ledger, not
`.gitignore`, and no tree, not even in `BEND_LIB`. With no ledger, one that
does not parse, a target that names nothing, or a `--rename` refused by the
ledger alone, it stops before asking the remote anything.

### Remove

`ez remove <name>` drops the dependency from the ledger, and from the
`.gitignore` allowlist with it. A vendored dependency's committed tree,
`.ez/lib/<hash>`, is removed too, unless another dependency still names that
hash. A name the ledger does not have stops `ez remove` with exit 1, and it
writes nothing, as `cargo remove` does.

## Lock

`ez lock` resolves every import and writes `ez.lock.toml`. Its output is a
function of the ledger and the committed tree, so someone who has just cloned
your repo can run `ez lock` and get your lock back to the byte, without
re-running `ez add` (EZ-DOC-3).

What it reads:

- the ledger;
- the `.bend` files `git ls-files` lists, so it refuses outside a git
  repository;
- the committed trees under `.ez/lib`;
- each git dependency's files at its ledger `rev`;
- hub content.

It takes the hub imports of every listed file and follows no local import, so
an untracked file never reaches the lock, even one a tracked file imports. It
does not record the bend that ran it, and without `--upgrade` it never writes
`ez.toml` (EZ-DOC-5).

Checks:

- Every package is checked against its `0x` name and every file against its
  sum, whatever it was read from.
- A tree already under `BEND_LIB` is judged as the same bytes cloned at the
  ledger's `rev` with the ledger's `narHash`.
- A git dependency whose tree is not under `BEND_LIB` at the ledger's `rev`
  is fetched, checked against `narHash`, and left there once the lock is
  written.
- A hash the ledger does not name is fetched from the hub. When the hub does
  not have it, the lock says the ledger does not name it and exits 1.
- A lock whose hashes, paths or values would not read back (a repeated hash,
  or a `"`, `\` or newline in one) is refused, and so is a package with a
  file whose path holds `=`.

A fetch or a check that fails stops the lock with exit 1, and a lock that
stops writes nothing: not the lock, and no tree.

Tool pins: `ez lock` records each `[tools.*]` pin in `ez.lock.toml`
(`[tools.bolt]`, say), copying `rev` and `narHash` from the ledger. A pin
missing either stops `ez lock` with exit 1 and names the command that fills
it, `ez lock --upgrade --package bolt`.

## Upgrade

`ez lock --upgrade` re-pins git dependencies and `[tools.*]` pins, then
writes the lock. `--package NAME` limits that to one dependency or one tool,
and every other ledger entry keeps its rev, tag and hash (EZ-RES-6).

- A `tag` is re-resolved (EZ-RES-8).
- A dependency with only a `rev` moves to the default branch tip when the
  pinned commit is an ancestor of it, and stays a commit pin. Otherwise the
  upgrade refuses (EZ-RES-5).
- A hub dependency does not move (EZ-RES-4).
- An empty tool pin is filled, its tag re-resolved and its `narHash` filled,
  the way a git dependency's is.
- A pinned commit whose tree no longer hashes to the pin is a drift, and
  stops the upgrade.

The upgrade itself fetches only the dependencies it re-pins. The lock it then
writes fetches any other git dependency whose tree is missing, the way a
plain `ez lock` does.

When a hash moves:

- A dependency marked `vendor` is laid out again under `.ez/lib/<new hash>`,
  its old tree is removed, and the `.gitignore` allowlist follows it. Any
  other moved tree is left under `BEND_LIB`.
- An import line that starts `import <old>/`, at column 0, is rewritten to
  start `import <new>/`, and no other line changes (EZ-VEN-2, EZ-VEN-3).

The upgrade and the lock are one plan: `ez.toml` is written once, then
`.gitignore`, the rewritten sources and the lock. An upgrade that stops, or a
lock after it that stops, writes nothing at all.

## Fetch and vendoring

### Fetch

`ez fetch` fills `BEND_LIB` from the lock, as `uv sync --frozen` does. Before
it lays anything it checks every file against the lock's sum, every package
against its name, and every git checkout against the `narHash` the lock
records (EZ-FETCH-1). It refuses with exit 1, writing nothing, when there is
no `ez.toml` or no lock, or when any check fails; a refused fetch lays no
tree, and removes none already under `BEND_LIB`.

`BEND_LIB` defaults to `.ez/lib`. bend looks in `~/.bend/lib` when it is
unset, so set it when you run `bend` yourself.

### Vendoring

A dependency is committed with the project when its ledger entry says
`vendor = true`. Its tree lives under `.ez/lib/<hash>`, and the hash is named
in `.gitignore`. Without `vendor = true` the tree is not committed, and
`ez fetch` or `ez lock` fills it in.

`ez add` records a new dependency without `vendor`; you set it by hand.
Adding the dependency again keeps it, lays the new tree under
`.ez/lib/<hash>` rather than `BEND_LIB`, and removes the old committed tree
when the hash moved and no other dependency names it.

### The .gitignore allowlist

The allowlist is derived from the ledger (EZ-VEN-1). After `ez add`,
`ez remove` or `ez lock --upgrade`:

- the `!.ez/lib/<hash>` lines of `.gitignore` are exactly the hashes of the
  dependencies marked `vendor = true`, each once, in the order the ledger
  first names them;
- every other line is left as it was, blank lines included;
- a missing hash is written where the first allowlist line was, or at the end
  of the file, and a hash the ledger no longer vendors is dropped;
- the file is only written when this changes it.

ez counts as its own any `!` line under `.ez/lib/`, however it is spelled (a
leading or trailing `/`, surrounding blanks), and writes the ones it keeps as
`!.ez/lib/<hash>`.

The allowlist needs `.ez/*`, `!.ez/lib` and `.ez/lib/*`, which `ez init`
writes. git cannot re-include a file under a directory it has excluded, so
under a bare `.ez/` no allowlist line works, and ez replaces that line with
the three.

## Check, build and run

- `ez check` checks the entry without running it.
- `ez build [out]` builds the entry to a native binary.
- `ez run [args..]` checks and runs the entry with bend, as `cargo run` runs a
  binary. The program reads ez's stdin and prints straight to the terminal as
  it goes, gets every word after `run`, and its status is the status of the
  command. The entry is the one `ez.toml` names, or `main.bend` when it names
  none (EZ-TOOL-9).

## Tools

The tool commands build and run another project's binary, whether that
project uses ez or is a plain Bend repository:

```
ez tool sync                      build and link every pinned tool, at its lock rev
ez tool run [--entry F] <target> [-- args..]
                                  fetch, build and run a repo's binary
ez tool install <target> [--entry F]
                                  build the binary and link it on PATH
ez tool upgrade <target> [--entry F]
                                  rebuild when the commit moved, refresh the link
```

A target is read as in [Targets](#targets). `ez tool run <target>` passes
every word after the target to the program, dropping one leading `--`, so
`--entry` goes before the target there, as uvx takes its own options before
the command.

```bash
ezx Emerging-Patterns/bolt -- --gpu off   # an ez project, built from its lock
ezx ./hello                               # a plain Bend repo: builds main.bend
ezx --entry src/cli.bend ./hello          # another file of the same checkout
```

### Pinned tools

A tool the project uses is a `[tools.*]` pin in the ledger:

```toml
[tools.bolt]
git = "https://github.com/Emerging-Patterns/bolt"
tag = "v0.4.0"
rev = "24b497e294a08f6a83e0b08ece3795f813421b87"
root = "."
narHash = "sha256-…"
entry = "bolt/main.bend"
```

A pin needs no `hash` and is never a dependency (EZ-LED-5). `ez lock` copies
it into the lock and `ez lock --upgrade` moves it (see [Lock](#lock) and
[Upgrade](#upgrade)). `ez tool sync` checks every pin against the lock before
it installs any, then builds and links each at the lock rev. It runs one
install per pin, so a later install that refuses leaves the earlier ones
installed, as `cargo install a b` does.

### What a target builds

A target resolves to a commit (EZ-TOOL-4):

- A name that matches a `[tools.*]` pin resolves to the rev in
  `ez.lock.toml`, which has to be a full commit. So `ez tool run bolt` uses
  the lock's rev, while `ez tool run owner/repo` is the repo's HEAD.
- A remote resolves to `git ls-remote <url> HEAD`.
- A path resolves to a clean `HEAD`. A worktree with uncommitted or untracked
  changes (untracked files count whatever the repository's own settings
  hide), or a path that is not the top of a checkout, has no commit and is
  built every time (EZ-TOOL-3).

The built file is the pin's `bin`, then the pin's `entry`, then the file
`--entry` names, then the checkout's `bin`, then its `entry`, then
`main.bend` (EZ-TOOL-7). So `--entry` picks another file of an ez project, as
cargo's `--bin` does, but does not move a pin, which the project decided. A
built file that is not in the checkout is refused before anything is
written, with a message that names it and suggests `--entry`.

### Plain Bend repositories

A checkout with no `ez.toml` is a plain Bend repository, and runs the way
`uvx` runs any package. It has no git dependencies and no lock, so ez builds
it with `BEND_LIB` set to a library of its own in the cache, `<slug>/lib`,
beside its binaries, and bend fetches the program's `0x…` and
`<name>@<version>` hub imports into it itself. Those are content-addressed,
so bend checks each against its name. A build that fails because bend could
not load an import says so on stderr, as any failed build does.

A checkout that has an `ez.toml` and no `ez.lock.toml` is an ez project whose
author has not locked it, and is refused with a pointer to `ez lock`.

### The cache

The checkout and the binary are cached under `$XDG_CACHE_HOME/ez/tool/<slug>`,
or `~/.cache/ez/tool/<slug>` when that is unset.

- The slug of a URL or of `owner/repo` drops a trailing `.git`. A URL with no
  host, `file:///srv/repo`, is cached as `file://localhost/srv/repo` is. A
  slug that is empty, absolute, or climbs with `..` is refused (EZ-TOOL-8).
- A remote's checkout is kept per commit, under `<slug>/<rev>/src`, and
  reused while its `rev` record names that commit.
- Every binary is kept under `<slug>/bin/<record>/`, named by its `key`: that
  commit, the built file and `bend version` (EZ-TOOL-2). So a pin's `bin` or
  `entry`, a free run of the same repository at another commit, and a new
  bend each build their own binary, and none rebuilds another's.

### run

`ez tool run` builds the binary and runs it, as `cargo run` does. It says on
stderr what it resolves and builds, and a build that fails shows bend's output
there too. Then the built program reads ez's stdin and prints straight to the
terminal as it goes, and its status is the status of the command (EZ-TOOL-5).

`ezx <target> [-- args..]` is `ez tool run`. The nix install provides it; to
make one yourself, see the [README](../README.md#install).

### install and upgrade

`ez tool install` fetches the lock, for an ez project, and builds
`<slug>/bin/<record>/<name>.out`, then links that file onto PATH as
`<name>`. Each long step says what it is doing before it waits, and on
success the command names what it installed and where the link is.

`<name>` is the package name in the target's `ez.toml` (`bolt` for bolt), or
`app` when the ledger names none. For a plain repository it is the built
file's name without `.bend` (`cli` for `src/cli.bend`), or the repository's
name, the last segment of its URL or path with `.git` dropped, when that is
`main`. A name that is not a TOML bare key is refused.

The link goes in the first of these that is set and nonempty (EZ-TOOL-1):

1. `$EZ_TOOL_BIN/<name>`
2. `$XDG_BIN_HOME/<name>`
3. `~/.local/bin/<name>`

The directory is created when it is missing. With none of the three, install
and upgrade refuse before anything is built.

`ez tool upgrade` reads that commit again, builds it when no binary is kept
for its record, and writes the link again. A binary already built for that
record is left in place. Neither install nor upgrade runs the binary
(EZ-TOOL-6).

A target, ledger, fetch, build or link that fails exits 1, and a command that
refuses writes nothing: no checkout, no binary, no link.

## The hub

Hub packages come from `https://hub.bend-lang.com`, or from the hub a `hub`
key in the ledger's `[package]` table names. The lock records that hub, and
`ez fetch` fetches hub packages from it. `ez lock` does not read `BEND_HUB`.

### Named imports

A hub package can be imported by name, as bend 2.0.26 and later allow:
`import <name>@<version>/file.bend as P`. `ez add` records one:

```bash
ez add bend-tensors@0.0.0.2          # or: ez add bend-tensors@0.0.0.2 lib.bend
```

It asks the hub the ledger names (`[package] hub`) for the hash the name
names, fetches that package, checks its manifest hashes to that name, lays
it under `BEND_LIB` with the name's file beside it, and records a dependency
with `hub = "<name>@<version>"` and its `hash`:

```toml
[deps.bend-tensors]
hash = "0x39d8166231e68361eb37e8bef9287b8a"
hub = "bend-tensors@0.0.0.2"
entry = "tensors.bend"
```

Then it prints the hash and the line to import it by,
`import bend-tensors@0.0.0.2/tensors.bend as Tensors`. The key is
`--rename NAME` when given, else the key ez.toml already gives that name at
any version, so adding another version replaces it, else the name before the
`@`. A key ez.toml gives any other dependency is refused. The word after the
name is the entry, since the version is already pinned. With none, the entry
is the package's `main.bend`, else its first top-level `.bend` file, else none
is recorded and no import line is printed. A name the hub does not have, a
package that does not hash to it, and an entry the package lacks are refused,
and a refused add writes nothing. You can also write the section by hand.

`ez lock` pins every name to its hash under `[names]` in ez.lock.toml. It asks
the hub only for a name that neither ez.toml nor the lock already records,
which happens only for names a dependency imports. A named import in your own
files must be in ez.toml, or `ez lock` refuses. `ez lock` and `ez fetch`
write `BEND_LIB/names/<name>@<version>`, the file bend reads a name from, so
bend never asks the hub at build time; `ez fetch` rewrites one that names
another hash and says so. `ez doctor` fails when a names file is missing or
names another hash. A name is a pin: `ez lock --upgrade` does not move it,
since the hub cannot list a name's versions.

## Publish

`ez publish` sends the entry to the hub with `bend --publish`, under ez's own
`0x` name. Publishing is irreversible and public, so every check that can be
made before the upload is made first:

1. there is a ledger that parses, and it names the entry, and the name it
   publishes under, if any, is one bend takes (EZ-PUB-3);
2. `git status --porcelain --untracked-files=normal` names no path, and git
   could answer it (EZ-PUB-1);
3. the walk from the entry makes a package;
4. git tracks every file of that package, unchanged (`git ls-files -v` tag
   `H`), so an ignored file is refused too;
5. every hub package the package imports is on the hub (EZ-PUB-5).

For the last check ez reads the hub imports of the package's files, each
`0x<hash>/...` and each `<name>@<version>/...`, and asks the hub the ledger
names (`[package] hub`) about each, as `ez lock` does: the hub must serve a
manifest that hashes to the `0x` name, and must resolve a name to a `0x` name,
the one `ez.lock.toml`'s `[names]` or ez.toml records for it when either does.
A package on the hub is built from the hub alone, so one that imports a
dependency you vendored from git, or a name the hub does not know, is refused,
as `cargo publish` refuses a dependency that is not on crates.io:

```
ez: the package imports hub packages that https://hub.bend-lang.com does not have, or could not be asked about, and a package on the hub has to build from the hub alone, so nothing was sent:
  0x04b9afdd6d6a56039c5ce6dfb1e55294 (eztoml, git https://github.com/Emerging-Patterns/eztoml) is not on the hub; publish it first
```

Every missing import is named, with the dependency's key and origin when
ez.toml records it. A hub that cannot be reached, or that answers with
anything but the package or a 404, refuses too, since what cannot be checked
is not sent. A package with no hub import asks the hub nothing.

Only then does bend upload. Just before it does, ez prints, on stderr, the
line the hub will describe the package by:

```
hub description: # demo: a demo
```

The hub takes the first line of the package's first file by path, in plain
string order, so an uppercase letter comes before every lowercase one, and
passes over every file named `LICENSE`. The package's files are the entry,
the files it imports, and the `LICENSE` beside each, so the line is the
entry's first line unless a file it imports sorts before it: an entry
`main.bend` importing `lib/util.bend` is described by the first line of
`lib/util.bend`. The line comes as bend starts, not as a question: to change
it, stop bend while it mines its proof of work, edit the file, commit, and
publish again. A publish refused before the upload prints only why
(EZ-PUB-4).

bend cannot report a package's hash without
uploading it, so its answer is checked after: ez succeeds only when bend exits
0, a line of its output is exactly a `0x` name, and every such line equals
ez's own hash. It then prints that hash and the import line for the entry's
path inside the package. Any other answer exits 1, with no import line
(EZ-PUB-2).

`bend --publish` reads the hub from `BEND_HUB` itself, while ez checks the
imports against the hub the ledger names. Both are
`https://hub.bend-lang.com` unless you set one, so a project that publishes to
another hub names it in both places.

### Publishing by name

A package can also go on the hub under a name, so that others import it as
`<name>@<version>` (see [Named imports](#named-imports)). Give the ledger's
`[package]` table both keys:

```toml
[package]
name = "tensors"
entry = "tensors.bend"
publish-as = "bend-tensors"
version = "1.2.0"
```

`ez publish` then runs `bend tensors.bend --publish bend-tensors@1.2.0.0`,
which publishes the package and names it in one run, and on success prints
the hash and `import bend-tensors@1.2.0.0/tensors.bend as Tensors`. bend asks
you to `bend login` the first time, and the hub refuses a name that is
someone else's or a version that does not go up.

- `publish-as` is a hub name, as bend's rule reads one: a lowercase letter,
  then a-z, 0-9 and `-`, 12 to 64 characters in all. It is not `name`, which
  is the ledger's own and may be anything, and not `hub`, which is the hub's
  URL.
- `version` is `MAJOR.MINOR.PATCH`, three numbers with no leading zeros.
  bend's versions have four numbers, so ez publishes `1.2.0` as `1.2.0.0`. A
  pre-release or build suffix, such as `1.2.0-rc.1` or `1.2.0+abc`, is
  refused: the hub has no way to write one.
- With only one of the two keys, or with either one malformed, `ez publish`
  refuses with exit 1 before it asks git anything or runs bend, and says which
  key is missing or wrong.
- With neither, it publishes by hash as above.

## Doctor

`ez doctor` reports on the toolchain and the project, and never writes to
your source (EZ-VEN-4). It reports:

- the versions of `bend`, the C compiler (`$CC` when it is set, else `cc`)
  and `git`;
- the ledger: the package, its entry and how many dependencies it names;
- what the lock names, and whether every locked package is under `BEND_LIB`;
- whether the lock is up to date: it runs a plain `ez lock` without the
  network, over the ledger, the committed sources and the trees under
  `BEND_LIB`, and compares the text with `ez.lock.toml` byte for byte, as
  `cargo --locked` and `uv lock --check` do. A lock that is stale, one
  `ez lock` would refuse to write, or one it cannot judge because a package
  is missing from `BEND_LIB`, fails the command (EZ-VEN-6);
- drift: every hash an import line names that the ledger does not, and every
  ledger dependency no import line names (EZ-VEN-5). It never rewrites your
  source to fix it.

It exits 1 when it reports any problem, after reporting everything it found.

## Nix

In a flake, `lib.${system}` builds the program the ledger names and turns
`ez.lock.toml` into a `BEND_LIB` store path, so there is nothing to copy into
your repo:

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

- `mkPackage` builds `bin` from `ez.toml` when that is set, otherwise
  `entry`, otherwise `main.bend`, and wraps the binary with `bend` on `PATH`.
  - `lock` is an explicit lock path.
  - `bendLib`, when set, is the store path used as `BEND_LIB` and wins over
    that lock.
  - With neither, `BEND_LIB` comes from `src/ez.lock.toml` when that file is
    present.
- `ez.bendLib ./ez.lock.toml` is that tree on its own. Every file comes from a
  fixed-output derivation keyed by the sha256 the lock already records, so
  the build needs no network and `bend` never reaches the hub.
- `mkProofs` runs `ez prove` over a copy of `src`. This repo's own `proofs`
  check is that.
- `mkLint` builds `bolt` from `[tools.bolt]` in the lock.
- `toolPackage` builds one locked tool, and `devPackages src` builds every
  one.
- `mkShell` puts those on `PATH` when `src` is set.

None of these need `inputs.bolt`.

This repo's `fresh` check (`mkFresh`) is a clone with no network:
`sh bootstrap.sh` over that tree fetches nothing, the build in the README
builds, and `ez lock` with `ez.lock.toml` deleted writes it back byte for
byte. CI also follows the README's install steps without nix and runs
`ez prove`.

## Prove and test

### prove

`ez prove` is the gate. It runs `bend` on every `PROOF.bend` in the tree, all
at once, and passes a proof only when the first line bend prints is exactly
`All terms check.`. bend exits 0 on a proof that leans on unsafe or foreign
code, so the exit status is not enough.

It prints a line for each proof and then the count, and exits 1 when any
proof failed. Nothing is cached, so every run checks every proof.

### test

`ez test` runs every `*/tests/*.bend`, each as its own `bend`, all at once,
and holds each run's output to the `#|` trailer at the end of its file.

This repo's tests are the end-to-end tests under `tests/`, which drive real
git daemons, `bend --publish` and `nix-build`, so CI does not run them.

### Limits

These variables apply to both `ez prove` and `ez test`:

- `EZ_CAP` sets the memory cap each `bend` runs under.
- `EZ_JOBS` sets how many run at once. It defaults to your cores, and never
  to more of them than the memory cap divides the machine into, since any one
  `bend` may claim the whole cap.
- `EZ_DEADLINE` is `ez test`'s budget in seconds, or `0` for no budget. The
  default is five minutes for a whole run, and a run that takes longer fails
  on that the way a test that printed the wrong line fails.

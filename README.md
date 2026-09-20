# ez

Build orchestration for [Bend 2](https://github.com/bendlang/bend). Right now
that is one job: make a Bend project with hub dependencies build inside a Nix
sandbox, where there is no network.

```
ez init myapp main.bend             write an ez.toml for a new project
ez add <url> <ref> <entry.bend>     vendor a git package and record it
ez remove <name>                    drop a package from the ledger
ez lock                             resolve every import, write ez.lock.json
ez fetch                            fill BEND_LIB from the lock
ez check                            check the entry, without running it
ez build [out]                      build the entry to a native binary
ez run [args..]                     check and run the entry
ez test [--js-only]                 run every */tests/*.bend, on both lanes
ez doctor                           report on the toolchain and the project
```

`bend ez/main.bend -o bin/ez.bin` is the whole build, and `./bin/ez.bin test`
is the whole gate: every test, on the JS and the native lane. With nix,
`nix run .#` or `nix profile install .#` instead, and `nix develop` for a shell
with bend, bun, curl and `BEND_LIB` already set. `nix flake check` runs the
unit tests in the sandbox.

One step comes before both of those, and it is the only one that cannot be ez.
ez's own source imports sha256 out of `BEND_LIB`, and a fresh checkout has no
`BEND_LIB`, so a clone has to have its packages filled in once before any Bend
here will even check. `nix develop` does that. Outside nix it is one command
against the lock, and it is the last thing in this repo that has to run before
ez exists.

The subcommand is the binary's first argument. A compiled Bend binary gets its
own command line from `IO.args()`: the runtime keeps `--threads`, `--gpu`,
`--gpu-build` and `--help` for itself and strips them wherever they appear, and
everything after a `--` reaches the program untouched, those four included. On
the interpreted lane (`bend f.bend a b`) positional arguments still arrive, but
bend's own CLI rejects flags it does not know, so a flag wants the compiled
binary. `IO.args()` carries no argv[0], so a binary cannot locate itself: that
is what `EZ_ROOT` is for, and it goes away with the last of the TypeScript.

Packages are vendored per project rather than into `~/.bend/lib`, so `BEND_LIB`
is `.ez/lib` unless it is set. Base has `get_env` and no `set_env`, so ez tells
the bend and bun processes it starts by running them as `env BEND_LIB=... bend
...`; `env` is coreutils and is execvp'd like any other program, so no shell
appears anywhere.

In Nix:

```nix
bendLib = pkgs.callPackage ./nix/bend-lib.nix { } ./ez.lock.json;
# ... buildPhase = "BEND_LIB=${bendLib} bend main.bend -o app";
```

## Depending on a repo that never published

`bend --publish` is per entry file, and the `0x<hash>` it produces is a pure
function of that file and everything it imports. Nothing about it needs the hub.
So ez computes the hash an unpublished repo *would* get, and lays the package
out under that name:

```
bun bin/ez-git.ts https://github.com/owner/repo <40-char rev> src/lib.bend
# 0x7e63a5b990a375c304ed462c071214a6
# import 0x7e63a5b990a375c304ed462c071214a6/lib.bend as Lib
```

Paste that import line into your source and build. The import is the same line a
published package would have given you, so if upstream publishes that exact tree
later, the hash matches and the hub just starts serving it. Nothing in your
source changes.

`ez.lock.json` records the git url and rev instead of the hub for that package,
and `nix/bend-lib.nix` rebuilds it with `fetchgit`. `tests/git.bend` runs the
whole path against a served fixture repo and compares the nix tree against the
vendored one file by file.

`tests/publish.bend` keeps the hash honest. It runs real `bend --publish`
against a local hub and fails if ez's hash differs from the one bend mines.
That test is the reason this is safe to rely on.

The two alternatives, for comparison. You can publish their code yourself, since
the hub has no ownership and any tree can be published by anyone, but that puts
someone else's work on a public hub and still needs the network. Or you can
vendor the repo and use a relative import, which works today and needs no tool,
but leaves the dependency uncontent-addressed and unpinned.

## The ledger

Bend's content addressing answers *how a package is fetched*. Nothing answers
*which packages this repo depends on*. An import line carries a bare
`0x7e63a5b990a375c304ed462c071214a6`, scattered across whatever files use it. It
does not say what the package is, where it came from, or whether a newer commit
exists. `ez.toml` is that list.

```toml
[package]
name = "myapp"
entry = "src/main.bend"

[deps.json]
hash = "0x1111111111111111111111111111aaaa"

[deps.wire]
hash = "0x7e63a5b990a375c304ed462c071214a6"
git = "https://github.com/owner/repo"
rev = "16773c0aa9914b5f04d062469d50100111eb9c9c"
tag = "v1.0"
entry = "src/lib.bend"
```

A dependency with no `git` key lives on the hub. One with a `git` key was
vendored from a commit, and `tag` records what a human asked for, so an upgrade
knows what to re-resolve rather than guessing.

The hash appears both here and in the import lines, so they can drift. ez treats
the manifest as the record and the import lines as the truth, and reports a
disagreement rather than rewriting your source. Rewriting is a thing ez could do
later, behind an explicit command.

The TOML is a deliberate subset. Sections, comments, and `key = "value"` pairs,
because every value a dependency carries is a string. No arrays, no inline
tables, no numbers.

## Written in Bend

The manifest (`manifest/`) and sha256 (`sha/`) are Bend, tested the way bolt
tests: each `tests/*.bend` ends in the `#|` lines its run must print, and
`ez test` checks them on the JS lane and the native CPU lane.

sha256 is [Giulio2002/bend-sha256](https://github.com/Giulio2002/bend-sha256),
which proves its output equal to an executable FIPS 180-4 specification. It was
never published to the hub, so ez depends on it the way this README describes:
pinned to a commit, vendored under the hash `bend --publish` would have given it.
ez is its own first user. `sha/tests/hex.bend` checks the two FIPS vectors and
one real manifest line, whose digest is the package hash `0x182e9ab8...` that
`tests/hub.bend` builds against.

`run/` is the foreign effects, each a program run with its arguments, each with
a C and a JS twin. `R.exec` waits for what it runs and hands back its status and
everything it printed. `R.start` waits for nothing: it forks the program into a
session of its own with `/dev/null` for all three streams and answers with its
pid. That second one exists because a test that needs a server beside it cannot
wait for the server, and because a program left holding the pipe `R.exec` reads
would never let that read finish.

`hub/` is the fetch and the integrity check on top of them: a body is accepted
only when its sha256 starts with the hash that named it, which is the rule bend
itself applies.

One effect covers both HTTPS and git, and that is forced rather than chosen.
bend links its binaries with exactly `-std=c11 -O3 -lpthread -lm`, plus `-lX11`
or `-lasound` when the generated C includes those headers. Nothing else can be
linked, so a TLS client cannot live in C here. curl and git already speak those
protocols and are on the PATH, so ez runs them.

Arguments reach the effect newline separated and go straight to `execvp`, never
through a shell, so a url or a rev out of a lockfile cannot become shell syntax.
`run/tests/exec.bend` asserts that.

`ez/` is the command line, `io/` is whole-file read and write over Base's
chunked handles, `check/` is what the tests share, and `manifest/render.bend`
writes a ledger back out. What ez reads renders back byte for byte, which is
what makes `ez add` and `ez remove` safe to run on a file a person edits.

`ez-lock`, `ez-git`, `ez-restore` and `pkg` are still TypeScript, and `ez` runs
them through the same process effect it uses for curl and git. They get
replaced underneath the command line rather than beside it. What is left is the
import walk: reading local `.bend` files, following their imports, and writing
the tree into BEND_LIB. `EZ_ROOT` is how the binary finds them, and it is the
last thing about ez that a wrapper has to set.

### A gotcha worth knowing

`bend f.bend -o out` is how you check a file without running its main, and its
exit status is the verdict, with one exception. A file with no main checks
clean and then exits 1 with `Error: no main to run` from the emit. A check
failure throws before the emit, so that message can only follow a check that
passed. A clean file with a main prints nothing at all, so "it said nothing" is
success, not a missing signal.

Bend's own check report changed between releases. 2.0.16 prints
`All terms check, with N unsafe annotations.`; 2.0.18 prints
`All terms check, but N defs rely on unsafe or foreign code:` and a `- <name>`
line each. A test comparing a run's output has to drop both, which is what
`ez/quiet.bend` does for `ez test` and `bin/quiet.awk` for the flake. The local
gate runs 2.0.16 and the flake runs 2.0.18, so this showed up only in the
sandbox.

A compiled Bend binary does take arguments. It was not always so — 2.0.5 did
not pass them on, and the belief outlived it — but 2.0.16's `IO.args()` hands a
binary everything on its command line, positional or flag, minus the four the
runtime keeps and minus argv[0], which is never there at all. The interpreted
lane is the asymmetric one: `bend f.bend a b` passes positional arguments
through, while a flag it does not know is bend's own CLI error.

A Bend module reached through a path with a hyphen in it breaks the JS backend.
`import ./bend-sha256/sha256.bend as S` compiles to a JS identifier containing
`-` and dies with `SyntaxError: Unexpected token '-'`. Renaming the directory
fixes it. Vendoring under `0x<hash>/` sidesteps it, since a hash has no hyphen.

## The test runner

Bend has no `bend test`, so `ez test` is one. It finds every `*/tests/*.bend`,
reads the `#|` trailer that says what the run must print, runs the file on the
JS lane and then compiled to a native CPU binary, and compares. `--js-only`
skips the native lane, which spends a C compile per test. Anything that
disagrees fails the command, and the last line is always `PASS: n / total`.

A failure prints what was expected and what was observed, both in full, rather
than a diff. A diff is real work in Bend and a test's trailer is a handful of
short lines, so the pair says as much and costs nothing.

`ez test` is also the gate this repo commits behind, so it runs more than unit
tests. The `tests/*.bend` at the top level drive the real tools end to end: a
git daemon, a local hub, a real `bend --publish`, `nix-build`. They are found
the same way every other test is, and `check/world.bend` is what they share —
a temporary directory, a free port, a command run somewhere else, a server
started and stopped. They run on the JS lane only. The second lane compiles the
test, and what these tests drive is git, nix and bend itself: compiling the
driver twice runs those tools twice over to learn nothing new about them. A
unit test, whose subject is the Bend, still runs on both. The flake's check
uses the glob `*/tests/*.bend` and so reaches only the unit tests, because a
nix sandbox cannot run nix.

`ez/quiet.bend` is `bin/quiet.awk` in Bend: bend prints its check report after
a run, in one of two wordings, and neither belongs in what a test asserts.
Comparison ignores trailing blank lines, the way a shell's `$(...)` does, so a
trailing newline is never the difference.

## The doctor

`ez doctor` reports on what would stop this project from building, and exits
non-zero when something is wrong. Each line says what was found, not that it
passed: which `bend`, which C compiler and whether `$CC` chose it, whether the
two programs the one foreign effect reaches for are on the PATH, what
`ez.toml` says, how many packages the lock names, and whether `BEND_LIB`
holds every one of them.

The check worth having is the last one. A package hash is written in two
places, the `[deps.<name>]` section and the `import 0x...` line that uses it,
and nothing keeps them equal. ez reports the disagreement in both directions.
A hash the source imports that the ledger never names is one. A ledger entry no
import line uses is the other. It rewrites neither, because the manifest is the
record and the import lines are the truth.

The lock is read by grepping it for `0x` hashes rather than parsing it, so its
format is not doctor's business. Its name is `lock()` in `ez/doctor.bend`, once.

## Why only this

The `ez` design spec was written for a hypothetical proof language. Bend 2.0.16
already answers most of it, and measurement kills the rest. What survives is
the Nix gap.

**Bend already ships the package manager.** `bend f.bend --publish` hashes the
file and its local imports into `0x<32 hex>` and uploads them to
`hub.bend-lang.com`. `import 0x<hash>/main.bend as P` fetches that package and
checks it against the hash. There are no versions, so there is nothing to
resolve, and the import graph is already a closed, transitive, exact pin. A
separate lockfile format, a registry index, a yank flag and a resolver all have
no work left to do.

**The expensive phase is codegen, not checking.** The spec assumed elaboration
dominates, the way it does for Lean, and built a target-independent check cache
around that. On bolt (127 files, 9562 lines) the measured split is the other
way round.

| Phase | Time |
|---|---|
| check and emit JS | 3.9 s |
| check and emit C (7.4 MB) | 66 s |
| `clang -O3` on that C | 25 s |
| `core/PROOF.bend`, proofs only | 0.13 s |

The C backend is whole-program and target-dependent, so a content-addressed
cache over it caches one fat artifact that any source edit invalidates. That is
the narrow, low-hit-rate case the spec warned about in its own open question 4.
A check cache would save 4 seconds out of 95. Neither earns its place yet.

Two runs of `bend bolt/main.bend -o a.c` produced byte-identical output, so
codegen is deterministic on a fixed machine.

**The Nix gap is real and nothing upstream fixes it.** `bend` resolves hub
imports during the check, inside `book_load`, by fetching into
`$BEND_LIB` (default `~/.bend/lib`). A Nix build cannot do that. The fix needs
no change to Bend: resolve the graph ahead of time, fetch each file as a
fixed-output derivation keyed by the sha256 the hub manifest already carries,
and point `BEND_LIB` at the resulting store path.

Proven end to end by `tests/nix.bend`: `nix-build` fetches through the lock, and
the build then runs with the hub unreachable.

## Still open, not built

- **Toolchain pinning.** `bend update` is `curl | sh`, and the installed version
  lives in `~/.bend/app/<version>/`. A project cannot pin it. bolt works around
  this by taking bend from `bendlang/bend`'s flake.
- **Ambient toolchain in native builds.** `cc_find` walks `PATH` for a clang,
  and the GPU decision comes from `$CUDA_HOME` and whether
  `/usr/local/cuda/include/nvrtc.h` exists. Same source, different machine,
  different binary. The emitted C is unaffected, so pinning `CC` closes it.
- **A test runner.** There is still no `bend test`. `ez test` is one, for this
  shape of test: a run's output compared against the `#|` trailer the file ends
  in. Nothing about it is known to Bend.
- **No hash re-check on a populated `BEND_LIB`.** `bend` skips the hub entirely
  when the file is already there, and does not re-hash it. Under Nix the store
  path is the integrity guarantee, so this is fine there, and worth knowing
  anywhere else.

## Layout

    ez.toml             the ledger: every package this repo imports
    ez.lock.json        the resolved closure, with each file's sha256
    flake.nix           bend, bun, the BEND_LIB from the lock, and the checks
    manifest/           ez.toml, read in Bend
    sha/                sha256, from a vendored package ez pins in its own ledger
    run/                the foreign effects: a program run, and one left running
    hub/                a file fetched and checked against the hash naming it
    bin/quiet.awk       drops bend's check report, for the flake's own check loop
    ez/                 the subcommands, and the dispatch behind bin/ez.bin
    ez/args.bend        the command line, as IO.args() hands it over
    ez/env.bend         BEND_LIB and EZ_ROOT, and how a child process is told
    ez/test.bend        the test runner: every */tests/*.bend, on both lanes
    ez/quiet.bend       bend's check report dropped, the way bin/quiet.awk does
    ez/drift.bend       the hashes in ez.toml against the ones the source imports
    ez/doctor.bend      the toolchain and the project, reported on
    io/                 a whole file read or written, over Base's chunked handles
    check/kit.bend      what a test asserts with
    check/world.bend    a scratch directory, a free port, a server to stop again
    bin/pkg.ts          the package and hash `bend --publish` would produce
    bin/ez-lock.ts      walks the import graph, writes ez.lock.json
    bin/ez-git.ts       vendors an unpublished git repo under its would-be hash
    bin/ez-restore.ts   fills BEND_LIB from the lock, without re-resolving
    nix/bend-lib.nix    ez.lock.json -> a BEND_LIB store path
    check/oracle.bend   a local stand-in for the hub, so --publish can be run
    tests/check.bend    the built binary against this repo's own ledger
    tests/cli.bend      every subcommand, through a project of its own
    tests/publish.bend  ez's hash must equal the one bend mines
    tests/hub.bend      two-level fake hub; lock, then build offline
    tests/git.bend      an unpublished repo, vendored and rebuilt through nix
    tests/nix.bend      the hub path through nix-build

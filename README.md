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
```

`./build.sh` puts `bin/ez.bin` behind the `ez/ez` script and links it into
`~/.local/bin`. With nix, `nix run .#` or `nix profile install .#` instead, and
`nix develop` for a shell with bend, bun, git, openssl and `BEND_LIB` already
set. `./gate.sh` runs every test on the JS and native lanes; `nix flake check`
runs the same in the sandbox.

A native Bend binary takes no arguments of its own, so the subcommand rides in
`EZ_CMD` and the rest in `EZ_ARGS`, one a line, the way bolt does it.

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
and `nix/bend-lib.nix` rebuilds it with `fetchgit`. `tests/git.sh` runs the whole
path against a served fixture repo and checks the nix tree byte for byte against
the vendored one.

`tests/publish.sh` keeps the hash honest. It runs real `bend --publish` against a
local hub and fails if ez's hash differs from the one bend mines. That test is
the reason this is safe to rely on.

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
`./gate.sh` checks them on the JS lane and the native CPU lane.

sha256 is [Giulio2002/bend-sha256](https://github.com/Giulio2002/bend-sha256),
which proves its output equal to an executable FIPS 180-4 specification. It was
never published to the hub, so ez depends on it the way this README describes:
pinned to a commit, vendored under the hash `bend --publish` would have given it.
ez is its own first user. `sha/tests/hex.bend` checks the two FIPS vectors and
one real manifest line, whose digest is the package hash `0x182e9ab8...` that
`tests/hub.sh` builds against.

`run/` is a foreign effect, a program run with its arguments, with a C and a JS
twin. `ez add` vendors a git repo, so git stays on the PATH and `run/` is how ez
reaches it. Arguments reach the effect newline separated and go straight to
`execvp`, never through a shell, so a url or a rev out of a lockfile cannot
become shell syntax. `run/tests/exec.bend` asserts that.

`net/` is the HTTP and HTTPS client, and `hub/` is the integrity check on top of
it: a body is accepted only when its sha256 starts with the hash that named it,
which is the rule bend itself applies.

HTTPS was curl's job and is not any more. bend links its binaries with exactly
`-std=c11 -O3 -lpthread -lm`, plus `-lX11` or `-lasound` when the generated C
includes those headers, so `-lssl` can never join that line. But nothing says a
library has to be linked: `net/effs/wire.c` and its JS twin open libssl at run
time with dlopen and take every symbol with dlsym, and a fixed link line has
nothing to say about that. Base's own sockets do not help either — `TCP.connect`
puts its host through `inet_pton`, so it reaches an address literal and no name
— so the effect resolves with getaddrinfo and connects the socket itself.

The client does one thing: GET a url and answer with the body. `net/url.bend`
and `net/http.bend` are pure, so the request format, the status line, the header
lookup and both body framings are tested with no server anywhere;
`tests/fetch.sh` stands a plaintext one up and drives the socket half on both
lanes. Two things are worth knowing. Content-Length and chunk lengths count
bytes while a Bend String counts code points, so the framing counts UTF-8 bytes
rather than `String.length`; a page with one accented character exposed this
immediately. And a body arrives through the runtime's UTF-8 decode, which is
lossy for bytes that are not UTF-8 — but that is the decode curl's output came
through too, and ez fetches only Bend source and manifest text, so nothing
changed and nothing is at risk.

Under Nix that library is on no search path, so the `ez` wrapper sets
`EZ_LIBSSL` at it and `SSL_CERT_FILE` at a CA bundle. When libssl will not open,
the error says libssl and says why, rather than arriving as a connection that
mysteriously failed.

`ez/` is the command line, `io/` is whole-file read and write over Base's
chunked handles, and `manifest/render.bend` writes a ledger back out. What ez
reads renders back byte for byte, which is what makes `ez add` and `ez remove`
safe to run on a file a person edits.

`ez-lock`, `ez-git`, `ez-restore` and `pkg` are still TypeScript, and `ez`
shells out to them through the same process effect it uses for git.
They get replaced underneath the command line rather than beside it. What is
left is the import walk: reading local `.bend` files, following their imports,
and writing the tree into BEND_LIB.

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
`bin/quiet.awk` does for the gate and the flake alike. The local gate runs
2.0.16 and the flake runs 2.0.18, so this showed up only in the sandbox.

A Bend module reached through a path with a hyphen in it breaks the JS backend.
`import ./bend-sha256/sha256.bend as S` compiles to a JS identifier containing
`-` and dies with `SyntaxError: Unexpected token '-'`. Renaming the directory
fixes it. Vendoring under `0x<hash>/` sidesteps it, since a hash has no hyphen.

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

Proven end to end by `tests/nix.sh`: `nix-build` fetches through the lock, and
the build then runs with the hub unreachable.

## Still open, not built

- **Toolchain pinning.** `bend update` is `curl | sh`, and the installed version
  lives in `~/.bend/app/<version>/`. A project cannot pin it. bolt works around
  this by taking bend from `bendlang/bend`'s flake.
- **Ambient toolchain in native builds.** `cc_find` walks `PATH` for a clang,
  and the GPU decision comes from `$CUDA_HOME` and whether
  `/usr/local/cuda/include/nvrtc.h` exists. Same source, different machine,
  different binary. The emitted C is unaffected, so pinning `CC` closes it.
- **A test runner.** bolt hand-rolls one in `gate.sh`: `tests/*.bend` files each
  end in the `#|` lines their run must print. There is no `bend test`.
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
    run/                a foreign effect: a program run with its arguments
    net/                the HTTP and HTTPS client, and the socket under it
    net/url.bend        a url in its scheme, host, port and path
    net/http.bend       a GET formatted, and a response taken apart
    net/wire.bend       the effect: one request out, one response back
    net/client.bend     the two joined: a url in, a body out
    hub/                a file fetched and checked against the hash naming it
    bin/quiet.awk       drops bend's check report, so a test sees only its output
    ez/                 the subcommands, and the dispatch behind bin/ez.bin
    ez/ez               the script people run; EZ_CMD and EZ_ARGS reach the binary
    io/                 a whole file read or written, over Base's chunked handles
    build.sh            bin/ez.bin, linked into ~/.local/bin as `ez`
    bin/pkg.ts          the package and hash `bend --publish` would produce
    bin/ez-lock.ts      walks the import graph, writes ez.lock.json
    bin/ez-git.ts       vendors an unpublished git repo under its would-be hash
    bin/ez-restore.ts   fills BEND_LIB from the lock, without re-resolving
    nix/bend-lib.nix    ez.lock.json -> a BEND_LIB store path
    tests/oracle.ts     a local stand-in for the hub, so --publish can be run
    tests/publish.sh    ez's hash must equal the one bend mines
    tests/hub.sh        two-level fake hub; lock, then build offline
    tests/git.sh        an unpublished repo, vendored and rebuilt through nix
    tests/nix.sh        the hub path through nix-build
    tests/fetch.sh      the client against a server it starts itself

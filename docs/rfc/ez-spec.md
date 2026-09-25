# RFC: A Behavioral Specification for ez

## Draft Status

State: Draft

The first draft was written from the README, the PR history, and the Bend LAWS/PROOF conventions, without the source. This revision replaces those assumptions with what the code at `b28ca2c` does, and records the decisions a maintainer made on every point where the code and the intent differed. The evidence came from a companion inventory that listed every law ez had, what each one pointed toward, and what we found reading each command. The inventory then tracked every work package until the specification was met, and it has since been folded into this document: the map from requirement to laws is `SPEC.md`'s Law column, the planner as it was built is under "The planner as built", what is still open is under "Known gaps", and the history is under "How we got here".

Every review item below is resolved. Several decisions change ez's behavior; they are collected under "Decided behavior changes" and have landed as their own PRs. Every Proved requirement is proved.

Items for review:

- [x] <!-- REVIEW (resolved): Function names in the law sketches were placeholders. They now name real definitions, or say that none exists yet; see "Names used in this document". -->
- [x] <!-- REVIEW (resolved): The requirement list was derived from the README. Each requirement has been checked against the code, and requirements were corrected, added or removed to match. The notes under each requirement group below record what the check found. -->
- [x] <!-- REVIEW (resolved): bolt is the home for the traceability check, as a rule in its `laws` group beside `closed`, `law` and `unsafe`. -->
- [x] <!-- REVIEW (resolved): EZ-DOC-3 stays the headline guarantee. `ez lock` may read the ledger, the committed `.bend` files, the vendored trees, and hub content verified by hash, and nothing else. The changes that make that true are listed under "Decided behavior changes". -->
- [x] <!-- REVIEW (resolved, then reversed): `Sha.hex` first kept its low-byte fold, on the belief that EZ-HASH-4 needed it to match `bend --publish`. The publish check refuted it: `bend --publish` hashes with `crypto.createHash("sha256").update(text)` (bend2/main.ts `cli_publish`), which is the text's UTF-8 bytes, and the hub checks bodies with `TextEncoder` (bend2/bend.ts `hub_get`). A non-ASCII file published as a different hash from the one ez computed; snap, shake and ezhttp all hold one. `Sha.hex` now hashes the UTF-8 bytes, `Sha.raw` keeps the byte-level digest for NAR serials, and `tests/publish.bend` publishes a non-ASCII file so the gate catches a regression. -->
- [x] <!-- REVIEW (resolved): The gitignore allowlist is derived from the ledger by one pure function, called by `ez add`, `ez remove` and `ez lock --upgrade`. `ez init` writes `.ez/*`, `!.ez/lib` and `.ez/lib/*` instead of `.ez/`. EZ-VEN-1 is restored to "names exactly the vendored hashes". -->
- [x] <!-- REVIEW (resolved): No message prefix becomes a requirement. EZ-OUT-1 is the exit-status rule; wording is incidental. -->
- [x] <!-- REVIEW (resolved): Tag selection changes: a release beats any pre-release, the default branch is asked of the remote, and refs resolve exactly. EZ-RES-1 states the new behavior. -->
- [x] <!-- REVIEW (resolved): `owner/repo` allows `.` in both segments, so `vercel/next.js` is GitHub. EZ-RES-3 states the new behavior. -->
- [x] <!-- REVIEW (resolved): The tool cache key records the built file and the bend version beside the commit. EZ-TOOL-2 states the new behavior. -->
- [x] <!-- REVIEW (resolved): If bend can report a package's hash without uploading, `ez publish` compares before it uploads. If it cannot, the check stays after the upload and EZ-PUB-2 says so. bend 2.0.25 cannot, so the check stays after the upload. -->
- [x] <!-- REVIEW (resolved): The proof gate moves out of `ez test` into its own command, `ez prove`, which `mkProofs` runs. `ez test` may call it. -->
- [x] <!-- REVIEW (resolved): `SPEC.md` is the single requirement list. The bolt rule parses only its requirement table rows. -->
- [x] <!-- REVIEW (resolved): `mkLint` joins ez's flake checks now, with `[tools.bolt]` moved to v0.8.1 and `closed` and `law` at `warn` until the first rollout phase is done. `unsafe` stays at `error`. -->
- [x] <!-- REVIEW (resolved): bolt v0.8.1's `closed` rule accepts closed equalities (bolt#10), so it does not enforce "closed laws have no standing". ez asked bolt for an opt-in stricter setting rather than enforcing it in its own rule; bolt v0.9.0 added it as the `quantify` rule (L004), and ez turned it on. bolt has since made `closed` itself strict and retired `quantify`; ez deleted its trails and moved to that bolt, with `closed` at `error`. -->
- [x] <!-- REVIEW (resolved): bolt v0.8.1 reports about 900 style, correctness and suspicious findings in ez beyond the law rules. A preliminary phase fixes all of them before `mkLint` is enabled. -->
- [x] <!-- REVIEW (resolved): The thirteen refactor-equivalence laws, and the `old.*` definitions they compare against, are deleted in the first rollout phase. -->
- [x] <!-- REVIEW (resolved): Guarantees proved in a pinned dependency are Trusted from ez's side, with the dependency and pin as the reason. -->
- [x] <!-- REVIEW (resolved): Closed laws are deleted, not kept as examples. -->
- [x] <!-- REVIEW (resolved): The phase-three design, [ez-lock-planner.md](ez-lock-planner.md), is accepted with every recommendation it made. It rewords EZ-DOC-5 and EZ-RES-6, adds EZ-OUT-2, adds five behavior changes to "Decided behavior changes", and proves the phase-three upgrade laws relative to EZ-LED-4. -->
- [x] <!-- REVIEW (resolved): The design for converting `ez add` and `ez remove`, [ez-add-planner.md](ez-add-planner.md), is accepted with every recommendation it made. It rewords EZ-LED-8 for a `~/` target, and adds seven behavior changes to "Decided behavior changes". -->
- [x] <!-- REVIEW (resolved): None of the accidental behavior found while reading the code becomes a requirement. The fixes worth making are listed under "Decided behavior changes". The doctor drift report and argument forwarding, which had only closed laws, become EZ-VEN-5 and EZ-TOOL-9 instead of losing their only record. -->

---

## Abstract

ez has 269 laws across ten LAWS.bend files. 122 of them are closed equalities, most moved over from `#|` tests, so they pin exact outputs for specific inputs rather than stating what ez guarantees. This RFC defines a behavioral specification for ez in which every requirement is either **Proved** by a quantified law or explicitly **Trusted** as an assumption about the environment, with nothing in between. It adds a model of the state each command reads and writes, so that IO behavior can be stated as laws, and a refactoring contract that says exactly which statements a change must preserve.

That was ez when we wrote the first revision. Since then every command has been split into a pure planner and a thin interpreter, every Proved requirement has a tagged quantified law, and no closed law remains.

## Glossary

| Term | Meaning |
| :---- | :---- |
| Ledger | `ez.toml`. The human-edited record of the package, its `[deps.*]`, and its `[tools.*]`. |
| Lock | `ez.lock.toml`. The machine-written record of the hub, every package with its source and files, and every tool pin. Today it also records the bend version; that field is dropped (see "Decided behavior changes"). |
| Import closure | The files reached from an entry by following local module imports in each file's header and foreign bodies (`import "path"`) anywhere, stopping at hub imports. |
| 0x hash | `"0x"` followed by the first 32 hex characters of `Sha.hex` of a package's manifest. The manifest is one line per file of the import closure, `<sum> <path>`, sorted by path. Names a package on the hub and under `.ez/lib`. |
| narHash | The SRI sha256 of a checked-out tree in NAR serialization, with the top-level `.git` removed, as `nix hash path --sri` would report it. |
| World | A value that models everything a command can observe: files, git remotes and checkouts, the hub, environment variables, and the toolchain. |
| Planner | The pure part of a command. It reads a World and returns a plan of effects and an outcome. |
| Interpreter | The thin IO part of a command. It executes a plan against the real system. |
| Law | A claim in LAWS.bend, proved by a definition of the same name in PROOF.bend. |
| Quantified law | A law with binders (`for x: T`). It holds for every input of that type. |
| Closed law | A law with no binders. It holds for one specific input, which makes it a unit test checked at compile time. |
| Proof gate | For every PROOF.bend, `bend PROOF.bend` prints exactly `All terms check.` as its first line. |
| Proved | A requirement backed by a quantified law tagged with its ID, passing the proof gate. |
| Trusted | A requirement that is assumed, listed in the trust boundary, and checked by nothing in ez. |
| Requirement ID | A stable name such as `EZ-DOC-3` for one entry in this specification. |

## Background

### What ez does

ez is a project manager for Bend 2. Bend already hashes a file and its local imports into a 0x name and serves it from a hub. ez sits on top of that and manages a whole project: it scaffolds projects, vendors git dependencies, resolves the import graph into a lock, fills `BEND_LIB`, builds and runs entries, pins and installs tools, and publishes. It is written entirely in Bend, and it computes the 0x hash a repo would get even when that repo never published, so the import line it writes is the one a published package would have produced.

### How ez proved things when we started

Bend's verification model splits claims from proofs. LAWS.bend holds the statements, PROOF.bend holds a definition that proves each one, and `bend PROOF.bend` fails until every law is discharged. Proofs are terms built from pattern matching, recursion as induction, and equality rewrites. There are no tactics and no proof search.

A passing exit status is not enough. `bend` exits 0 and prints `All terms check, but N defs rely on unsafe or foreign code:` when a proof leans on an unchecked def, and a def that never returns proves anything. The gate ez runs reads the first line of output and accepts only the bare `All terms check.` That stricter reading is what we mean by the proof gate throughout.

When we started, the gate ran inside `ez test`, and it has since moved to its own command (see "The proof gate"). `ez test` found every PROOF.bend, ran `bend` on each alongside its test lanes, and reported a proof as passed only on that exact line. `flake.nix` ran `ez test --js-only --unit-only` through `mkProofs`, and that was the only place CI checked the laws. `ez test` cached a passed proof in `.ez/cache`, keyed on the bend version, `$CC`, and the hash of the proof's import closure; `mkProofs` builds from a clean copy of the source, so in CI the cache was always empty.

ez adopted this model through a series of PRs that moved "law-shaped" equalities out of `#|` test trailers and into LAWS/PROOF across the sha, pkg, lock, git, net, pub, manifest and ez areas. The result is uneven. A law-by-law inventory at `f009e42` counted 147 quantified laws and 122 closed ones. The quantified laws include one real guarantee (the 0x hash does not depend on the order files were found in), a strong model of the ledger, the HTTP client's framing, the decision functions of `ez publish`, a path algebra, and thirteen laws that hold a faster rewrite equal to the definition it replaced. Every law about upgrade decisions, lock rendering, import rewriting, the gitignore allowlist, target classification, NAR hashing and SHA-256 is closed. Of the 94 laws in `ez/LAWS.bend`, 42 are about the `ez test` runner itself and 19 pin progress or error wording.

### Why this leaves us unsure what is proved

A closed law says `f(a) == b` for one `a`, and that has two consequences that pull in opposite directions.

Closed laws are too weak to protect behavior. A refactor that breaks `f` on every input except the witnessed ones still passes the gate. The gate gives the feeling of a guarantee without the substance of one, which is exactly the uncertainty we have today.

Closed laws are also too strong to allow change. A witness usually pins the entire output, including parts nobody depends on. `ez/LAWS.bend` has `hub_404_teaches`, which pins every word of one error message. A correct refactor that changes one of those details breaks the proof, and because nothing records which parts of the output were intended, we cannot tell a regression from an incidental change.

Reading the code against the README makes the point concrete. The README says `root` and `narHash` exist so that `ez lock` never has to consult anything a clone does not have. No law states that, and it is not true: a fresh clone of this repository does not reproduce its own lock.

## Problem Statement

We need a specification that answers two questions for every behavior ez has. What exactly is guaranteed? And is that guarantee proved for all inputs, or assumed? When we change the implementation, the answer must tell us mechanically which statements have to survive. Anything that is neither proved nor honestly labeled as an assumption is noise, because it looks like assurance and is not.

### Goals

- A single document listing every guaranteed behavior of ez, each with a stable requirement ID.
- Exactly two assurance levels: Proved and Trusted.
- An explicit model of the state ez commands observe and change, so that IO behavior can be stated as quantified laws.
- A refactoring contract based only on law statements and the trust boundary.
- Retirement of closed laws as a form of assurance.

### Non-goals

We are not proving Bend itself, git, the hub, nix, or the host filesystem correct; those are trust assumptions and the spec names them. We are not specifying `ez test`'s test lanes, and nothing in this specification depends on running a test. This RFC does not itself change ez's behavior. Where the spec and the current behavior disagreed, a maintainer decided which one is right; the resulting behavior changes are listed under "Decided behavior changes" and land as separate PRs.

### Scope

ez is a project manager first: it keeps a Bend project's ledger, lock, vendored packages and publishing honest. The tools area, `[tools.*]`, the `ez tool` commands and `ezx`, exists so that a project can pin the tools it runs, such as bolt, and after 1.0.0 it is frozen except for fixes. Two things are paused until the Bend ecosystem needs them: publishing ez itself to the hub, and installing a tool by its hub name. A bend package is an import closure, not a directory, so the hub carries libraries, and tools install from git. ez's own layout, with its entry at `manifest/manifest.bend`, stays as it is.

## Proposal

### Overview

The proposal has four parts. A **specification document** (`SPEC.md` at the repo root) lists every requirement with an ID, a level, and a status. A **World model** in Bend gives commands a pure form that laws can quantify over. **Law tagging** links every quantified law to the requirement it proves. A **refactoring contract** states which statements a change may touch.

|  |
|:---:|
| <pre>┌──────────┐     ┌───────────────┐          ┌────────────────┐     ┌────────────────┐<br>│ SPEC.md  │────▶│ Requirement   │──Proved─▶│ LAWS.bend      │────▶│ PROOF.bend     │<br>│ (IDs +   │     │ ID + level    │          │ (quantified,   │     │ (gate: "All    │<br>│  levels) │     │               │          │  tagged)       │     │  terms check.")│<br>└──────────┘     └───────┬───────┘          └────────────────┘     └────────────────┘<br>                         │<br>                      Trusted<br>                         ▼<br>                 ┌───────────────┐<br>                 │ Trust boundary│<br>                 │ (in SPEC.md)  │<br>                 └───────────────┘</pre> |
| Caption: Every requirement ends in either a quantified law the proof gate checks, or a named assumption. There is no third path. |

### Two levels, and why only two

Every requirement carries exactly one level.

| Level | Meaning | Backed by |
| :---- | :---- | :---- |
| Proved | Holds for every input in the model. | A quantified law in LAWS.bend tagged with the ID, passing the proof gate. |
| Trusted | Assumed about something ez cannot check from inside its own gate. | An entry in the trust boundary table. |

We considered intermediate levels for "checked on examples" and "agrees with an external oracle", and rejected both (see Abandoned Ideas). The short version is that Bend's gate is a proof checker, and anything it checks on a single example is a test wearing a law's syntax. Two levels keep the spec honest: if a claim is not proved for all inputs, we say we are trusting it, and a reader knows exactly how much weight to put on it.

A guarantee proved in a dependency is Trusted from ez's side. The SHA-256 digest comes from Giulio2002/bend-sha256, whose own laws hold it to an executable FIPS 180-4 specification, and HTTP framing is proved in ezhttp, which replaced `net/` in #50. Those proofs are real, but ez's gate does not re-check them, so ez records them as trust with the dependency and pinned hash as the reason.

A Proved requirement whose law has not landed yet is marked **pending** in `SPEC.md`. Pending is a status, not a third level: it means "intended to be Proved, not yet guaranteed", and the spec says so plainly. Because the gate fails on any undischarged law, a pending requirement's law stays out of LAWS.bend until its proof is written, and the statement lives in `SPEC.md` until then.

### The proof gate

The specification depends on one mechanical check: for every PROOF.bend in the tree, `bend PROOF.bend` prints exactly `All terms check.` as its first line. That check is its own command, `ez prove`, which does only that and which `mkProofs` in `flake.nix` runs. It was once the proof lane of `ez test`; `ez test` no longer runs proofs, and is outside the specification. The runner's faithfulness is a trust assumption (EZ-TRUST-4), in the same way the interpreter's is.

### The World model

Laws can only quantify over values, and most of ez's behavior is IO. We close that gap by modeling what a command can see as a value and splitting each command into a pure planner and a thin interpreter.

The fields below are what `ez lock` actually observed when we wrote this revision, taken from tracing the command (see "What ez lock may read"). This is the sketch we started from; none of these types existed in the code then. What we built differs in shape, and is summarized under "The planner as built".

```
# New types. Field names are proposals. Every field is something a command
# reads once the decided behavior changes land; today `ez lock` also reads
# .ez/origins.toml, BEND_HUB, and untracked files.
type World:
  ledger: String                      # ez.toml text
  tree: Map(Path, String)             # committed files, as `git ls-files` lists them
  lib: Map(Hash, Pkg)                 # manifests and files under $BEND_LIB
  env: Map(String, String)            # BEND_LIB, HOME, XDG_*, EZ_TOOL_BIN
  bend: String                        # the answer of `bend version`
  hub: Map(String, Maybe(String))     # GET <hub>/<hash>/<path>
  remotes: Map(Url, Remote)           # tags, heads, HEAD symref, ancestry, trees per rev

type Remote:
  refs: List(Pair(String, String))    # what `git ls-remote` prints
  head: String                        # HEAD symref target
  above: List(Pair(Rev, Rev))         # merge-base --is-ancestor answers
  trees: Map(Rev, Map(Path, Node))    # checkouts, with modes and symlinks, for NAR

type Effect:
  Write{path: Path, text: String}
  Lay{hash: Hash, files: List(Pair(Path, String))}
  Remove{path: Path}
  Print{text: String}

def lock_plan(w: World, a: LockArgs) -> Pair(List(Effect), Outcome)
```

The planner decides everything: which revs to pin, which files to write and with what bytes, what outcome to report, and what exit status to return. The interpreter reads the World and executes effects in order, and makes no decisions of its own. Requirements are stated over planners, which lets them quantify over worlds, and the interpreter's faithfulness becomes one explicit trust assumption instead of an unstated one scattered across every command.

|  |
|:---:|
| <pre>real system ──read──▶ World ──▶ planner (pure, laws apply) ──▶ Plan ──▶ interpreter ──▶ real system</pre> |
| Caption: All behavior lives in the planner, where laws apply. The interpreter only reads and performs effects, and is trusted. |

A World that holds whole remotes is a lazy value in spirit: the interpreter only needs to read the parts a planner asks for. For `ez lock` without `--upgrade` the planner reads `ledger`, `tree`, `lib`, `hub`, and `remotes` for the trees of non-vendored git dependencies at their ledger revs. With `--upgrade` it also reads remote tags, heads and ancestry, and `.gitignore` through `tree`. `bend` is read by `ez build`, `ez check` and the tool commands, not by `ez lock`.

We do not need to convert every command before the spec is useful. The spec is written against the model from the start, and each command moves to planner form when its requirements move from pending to proved.

### How far ez lock is from planner form

This is how the code stood at `b28ca2c`, before any conversion. Much of the pure half already existed. `origin` and `origins.all` choose where a package comes from (`lock/lock.bend:137-195`). `U.aim`, `U.judge`, `U.retarget`, `U.reallow.many` and `U.reimport.many` decide upgrades and compute the rewritten ledger, gitignore and sources (`manifest/upgrade.bend`). `Lock.render.tools` turns packages and tools into the lock's text. `K.hash_of` and `K.manifest_of` are pure.

What is not pure is the control flow between them, spread across roughly forty IO functions. Three places matter most. The package set grows from IO results: `resolve` reads or fetches a package, scans its text for imports, and queues what it finds, dying on the first bad package in walk order. A decision is made inside IO: `read.git` turns a missing manifest into an empty file list (`lock/lock.bend:287-293`), which is the bug that breaks EZ-DOC-3. And `--upgrade` runs three phases (`Up.run`, `Pin.upgrade`, `lock.now`) that communicate by writing ez.toml and `.ez/lib` and reading them back, so the final lock depends on the order of writes, and a failure in a later phase leaves earlier writes in place.

Converting `ez lock` means turning `roots` and `resolve` into a pure fold over `World.tree`, `World.lib` and `World.hub`, making the three upgrade phases one planner that threads the ledger through as a value, and moving the "missing tree" case out of `read.git` into an explicit outcome.

### The planner as built

Every command that reads or writes project state is now a planner and an interpreter: `ez lock` (plain and `--upgrade`), `ez add`, `ez remove`, `ez init`, `ez fetch`, `ez publish`, `ez doctor`, and `ez tool run`, `install`, `upgrade` and `sync`. Each lives in its own directory as `world.bend`, `plan.bend` and `run.bend` (`init/` and `remove/` need no World file of their own), beside the `LAWS.bend` and `PROOF.bend` that state and prove its requirements. The designs are [ez-lock-planner.md](ez-lock-planner.md) for the lock and [ez-add-planner.md](ez-add-planner.md) for the rest, which follow the lock's pattern.

The World is not the whole system as a value, as the sketch above has it. It is the few things a command reads up front (such as the ledger's text, the committed `.bend` files as `git ls-files` lists them, the arguments and the directory the command runs in) plus one answer for each question the planner has asked so far. A World has no field for anything the command may not depend on: `lock/world.bend` has none for the environment, the clock, the old lock, untracked files or `.ez/origins.toml`, so EZ-DOC-3 can be stated as a frame property over `W.inputs` and a regression that reads something new stops the proof.

The planner is pure and does one of two things with a World. Either it names the questions it still needs answered, or it returns a Plan. The lock asks for a package's manifest and files, from the hub, from `BEND_LIB` or from a clone at a rev; an upgrade, `ez add` and the tool commands also ask a remote for its refs, tags, default branch, ancestry or a checkout; `ez add <name>@<version>` asks the lock's own questions instead, what the hub says the name names and then that package (`add/hub.bend`, which `AP.command` runs for a name); `ez publish` asks what git tracks, then the hub about each hub package the package imports, reading the lock first when one is imported by name, and, last, for the upload. A Plan is a list of effects and an outcome. The interpreter loops, answering each question by one IO action and adding the answer to the World, until nothing is left to ask. Laziness costs no purity this way, since the planner only ever sees answers, and every source a question names is anchored by the planner, so the interpreter never decides where to look.

The lock's effects are `Write{path, text}`, `Lay{place, hash, files}` (a tree under `.ez/lib`, committed, or under `BEND_LIB`, a cache), `Drop{hash}` and `Say{text}`, and its outcome is `Success{}` or `Refused{why}`. A refused plan has no write, lay or drop in it, which is what EZ-OUT-2 says. `P.status` maps an outcome to the exit status, which is what EZ-OUT-1 is stated over. Every command but the tool commands runs its plan through the lock's effect runner, `Run.exec.plan` in `lock/run.bend`, which executes the effects in order and then exits through `Run.end` with that status. The tool commands have a plan of their own shape (the checkout laid, the binary made or reused, and then either the program started or the link written), and `TP.code` gives their status from the plan's end and the program's status; their writes still run through the lock's interpreter. The commands that are not planners (`ez check`, `ez build`, `ez run`, `ez test`, `ez prove`) end with an outcome `ez/ends.bend` computes from what bend answered, except `ez run`, which exits with the program's status (`S.code` in `ez/start.bend`). `ez/start.bend` decides from ez.toml what `ez check`, `ez build` and `ez run` start, or that they refuse, and `ez/line.bend` decides how a command line ends before any command runs.

The interpreters decide nothing, and that they read and execute faithfully is EZ-TRUST-2. Each one says in its header comment what it asks of the system, so the trusted surface can be read file by file.

The price of the loop is small. Measured on this repository's own lock when WP1 landed, with every tree already under `BEND_LIB`, a plain lock took 0.53 s against 0.21 s before, because every round re-scans the committed sources for imports; with every tree to clone, 7.4 s against 7.3 s, since the clones dominate. When WP2 folded the upgrade in, `ez lock --upgrade` against a real remote took 17.1 s against 20.7 s before.

### Names used in this document

The law sketches below use these names. Where no definition exists, the sketch introduces one.

| Name in a sketch | Real definition |
| :---- | :---- |
| `K.hash_of` | `pkg/pkg.bend:381`. The 0x name of a file list. |
| `K.pkg_of` | `pkg/pkg.bend:959`. Walks an entry's import closure and returns the package (IO): the pure walk `K.of` (`pkg/pkg.bend:856`), with each file it asks for read from disk. |
| `perm` | `pkg/LAWS.bend`. Lehmer-coded rearrangement of a file list; law vocabulary only. |
| `Nar.path` | `sha/nar.bend:538`. The narHash of a directory (IO): one `find` listing and each file's text, then the pure `Nar.tree` over them. |
| `Lock.render.tools` | `lock/lock.bend:630`. The text of `ez.lock.toml`. |
| `Lock.lock.at` | `lock/lock.bend:817`. The whole lock computation for a ledger and `BEND_LIB` (IO). Called from `Cmd.lock.now`, `ez/cmd.bend:193`. |
| `Lock.pack_of` | `lock/lock.bend:681`. A package of a parsed lock, by hash. |
| `M.find`, `M.tool.find` | `manifest/manifest.bend:274, 381`. A ledger entry by name. |
| `Up.one`, `Pin.up.one` | `ez/upgrade.bend:261`, `ez/pin.bend:272`. The per-dependency and per-tool upgrade (IO). |
| `U.aim`, `U.judge` | `manifest/upgrade.bend`. Whether a pin is asked of the remote, and what the answer means. |
| `U.reallow.many`, `U.reimport.many` | `manifest/upgrade.bend:213, 274`. The rewritten `.gitignore` and source text. |
| `M.parse`, `M.dep` | `manifest/manifest.bend`. A ledger read from text, and a dependency of a read ledger by name. |
| `World`, `Effect`, `LockArgs`, `Inputs`, `lock_plan`, `upgrade_plan`, `doctor_plan`, `inputs` | None. Introduced by this RFC. `upgrade_plan.ledger` is the ledger an upgrade plan writes, as a read ledger. |

### Requirements

The requirements below were the first version of `SPEC.md`, and the tables now carry `SPEC.md`'s current wording and status. Each one is stated as behavior, not implementation, and was checked against the code. The Status column is `proved` when a tagged quantified law exists and `pending` otherwise; today only EZ-LED-4 is pending. The notes under each table record what the code did when we wrote the requirement, what we decided, and how the row was proved.

We do not repeat the map from requirement to laws here. `SPEC.md`'s Law column is the canonical list of the tagged laws behind each row, bolt's `trace` rule checks it against the tags in every LAWS.bend, and `SPEC.md`'s "Left to prove" section says, for each row that took more than one command, how it was closed and what its laws rest on. A law named in the notes below is there to explain a decision, and the Law column is what to read for the complete set.

#### Hashing (EZ-HASH)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-HASH-1 | The 0x hash of a file list with distinct paths depends only on its (path, sum) pairs, not on the order they were found in. | Proved | proved |
| EZ-HASH-2 | The NAR serialization of a directory does not depend on the order its entries are listed in. | Proved | proved |
| EZ-HASH-3 | When ez writes a package under `<lib>/<h>`, `h` is the 0x hash of the file list whose manifest it writes beside the files. | Proved | proved |
| EZ-HASH-4 | ez's 0x hash for an entry equals the hash `bend --publish` assigns to it. | Trusted | |
| EZ-HASH-5 | ez's narHash equals `nix hash path --type sha256 --sri` of the same tree. | Trusted | |
| EZ-HASH-6 | `Sha.hex(s)` is the SHA-256 of the UTF-8 bytes of `s`. For a file's text that is SHA-256 of the file's bytes, which is what `bend --publish` and the hub compute. | Trusted | |
| EZ-HASH-7 | The NAR walk reads every name and symlink target as the tree listing prints it: nothing is trimmed, and a newline stays inside the name that holds it. | Proved | proved |

EZ-HASH-1 is already true and already proved. The law is `pkg/hash_perm`, over the file list the import walk produces rather than a directory tree, with distinct paths as a precondition:

```
# EZ-HASH-1
law hash_perm:
  for +ns: List<&2, Nat>
  for +xs: List<&2, P.File>
  for +dis: {distinct(xs) == True{} : Bool}
  {P.hash_of(perm(ns, xs)) == P.hash_of(xs) : String}
```

The precondition is part of the guarantee. `dedup` keeps the last of a run of equal paths, so two entries with the same path and different sums hash differently depending on order. The walk visits each file once, so distinct paths is what it produces, but the law does not cover the walk itself.

EZ-HASH-2 is true by construction: `sha/nar.bend` lists a directory with `find` and sorts the names with an insertion sort on `String.is_le` before serializing. It is not stated because the serializer reads the filesystem as it goes. Stating it needs a pure `Nar.of_tree(t: Tree) -> String` that `Nar.path` calls after reading, and then a law like the one above over permutations of each directory's entries. That is what we built in WP8 of the lock design: `sha/nar.bend` loads a directory's children in whatever order `find` lists them, `Nar.dir` sorts them with `K.file.sort` before serializing, and `sha/nar_dir_order_free` proves the result independent of the listing order for distinct names. The narHash of every package and tool in ez.lock.toml was recomputed with the new code and matched.

EZ-HASH-3 held when a tree was written, because `Git.lay` named the directory and wrote the manifest from the same file list. Nothing re-checked it afterwards, which is why it is stated about the write and not about the directory at rest. It is now proved for every command that lays a tree, `ez add`, `ez fetch` and `ez lock`, each of which checks that the files it lays hash to the name it lays them under.

The split in this group shows how the two levels work together. We cannot prove that ez agrees with nix or with Bend's publisher, because those are other programs, so EZ-HASH-4 and EZ-HASH-5 are Trusted. We know of ways EZ-HASH-5 can diverge, listed under "Known gaps". EZ-HASH-6 is restated from "computes FIPS 180-4 SHA-256" to say what is hashed: the UTF-8 bytes of the text. `Sha.hex` used to cut each character to its low eight bits, which is SHA-256 of the file only for ASCII. That fold was believed to be Bend's own, but a publish of a file with a non-ASCII character refuted it: `bend --publish` hashes `createHash("sha256").update(text)`, the UTF-8 bytes (bend2/main.ts `cli_publish`), so the fold broke EZ-HASH-4 for every package holding such a file. `Sha.hex` now encodes to UTF-8 before hashing, the same encoding `sha/nar.bend` always used, because both nix and Bend hash bytes.

The closed laws for the FIPS `abc` vector, the empty string and the empty NAR directory backed these requirements only as examples. They were removed in the first rollout phase.

#### Ledger (EZ-LED)

These requirements are new in this revision. The ledger code already has the strongest quantified laws in ez, and the draft did not list them.

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-LED-1 | A ledger that does not parse is never read into a model, and renders as nothing, so no command writes a guess over it. | Proved | proved |
| EZ-LED-2 | Adding a dependency to a ledger model twice is adding it once. | Proved | proved |
| EZ-LED-3 | Removing a dependency from a ledger model twice is removing it once. | Proved | proved |
| EZ-LED-4 | A ledger ez rendered parses back to the model it was rendered from. | Proved | proved |
| EZ-LED-5 | A `[tools.*]` section is a tool, never a dependency, and needs no `hash`. | Proved | proved |
| EZ-LED-6 | `ez init` writes nothing when a ledger exists, and `ez add`, `ez remove`, `ez fetch` and `ez lock`, with or without `--upgrade`, refuse and write nothing when there is none. | Proved | proved |
| EZ-LED-7 | A dependency's ledger name is `--rename` when given, which must be a TOML bare key; otherwise the name the ledger already records for that source; otherwise the target's `[package] name` when it is a TOML bare key; otherwise the repository's name; otherwise the directory's name. A hub package added by its `<name>@<version>` is named by `--rename` when given; otherwise by the name the ledger already records for a dependency added by the same name part, so another version replaces it; otherwise by the name part. A name the ledger gives a different source is refused, and so is a `--rename` of a source the ledger records under another name. | Proved | proved |
| EZ-LED-8 | A path target is recorded in the ledger as it was given, with a leading `~/` expanded, and a relative path resolves against the project root wherever git reads it: `ez add`, `ez lock`, `ez fetch` and `ez lock --upgrade`. | Proved | proved |

**Update (WP12):** EZ-LED-5 is proved over the ledger reader, which files a `[tools.*]` section among the tools, never among the dependencies, and never refuses it for lacking a `hash` (`tool_section_not_dep`, `tool_section_is_tool`, `tool_needs_no_hash`), and over every command that reads a ledger's dependencies: `ez lock`, plain or `--upgrade` (`lock_origins_skip_tools`, `upgrade_origins_skip_tools`), `ez add` (`add_keeps_tools`), `ez remove` (`remove_keeps_tools`, `remove_refuses_tool`) and `ez doctor` (`doctor_ignores_tools`).

EZ-LED-1 to EZ-LED-3 had quantified laws when we wrote them (`read_refuses_a_problem`, `render_of_unread_is_blank`, `add_idem`, `remove_idem`), and were pending only because the laws were untagged and stated the model edit, not the command. `ez add` did not call `R.add` on the parsed ledger: it forced `vendor = false` and re-rendered the whole file, so re-adding a dependency dropped `vendor = true`. Converting `ez add` and `ez remove` to planner form tied each command to its model edit (`add_edits_ledger`, `remove_edits_ledger`), and all three rows are proved. EZ-LED-4 had one closed example (`render_parse_roundtrip`), deleted with the other trails, and was the last row pending until WP21 proved it against the pinned eztoml v0.1.0 reader (`ledger_reads_back`), with every command that writes ez.toml refusing a ledger that would not read back.

EZ-LED-6 to EZ-LED-8 come from the decided behavior changes below. Their decisions are pure functions with quantified laws: for EZ-LED-6, `init_keeps_ledger` and `ledger_missing_unwritten`; for EZ-LED-7, `rename_wins`, `rename_dotted`, `rename_moved`, `rename_clash`, `name_keeps`, `own_package`, `own_invalid`, `leaf_is_last`, `clash_same`, `clash_other` and `clash_hub`; for EZ-LED-8, `anchor_url`, `anchor_absolute` and `anchor_relative`. We kept the three requirements pending until `ez add` and `ez remove` were in planner form, because the laws state what the decision functions return and not that the commands act on it. **Update (A2):** with `ez add` in planner form, EZ-LED-6 and EZ-LED-7 are proved by plan laws over each command (`add_needs_ledger`, `lock_needs_ledger`, `remove_needs_ledger`, `init_keeps_ledger`; `add_records_named`, `add_refuses_named`), and `ledger_missing_unwritten`, which was about the add half of `ez/cmd.bend`, is deleted with it. EZ-LED-8 has its `ez add` half (`add_records_as_given`, `add_path_as_given`, `add_asks_anchored`) and waits on the lock's questions and `ez fetch`. **Update (WP8):** `ez fetch` has its half too (`fetch_asks_anchored`, `fetch_keeps_records`), so EZ-LED-8 waited only on the lock's questions, which WP10 anchored, and the row is proved. EZ-LED-6 now names `ez fetch` beside `ez add`, `ez remove` and `ez lock` (`fetch_needs_ledger`, `fetch_needs_ledger_asks_nothing`). EZ-LED-8 is what keeps EZ-DOC-3 true for path dependencies: the ledger and the lock record the path as the user gave it, so a clone that keeps the project and the path's repository side by side locks to the same bytes. The one exception is a leading `~/`, which `ez add` expands when it records the path: a `~/` left in the ledger would make every later lock read `HOME`, which EZ-DOC-3 does not allow.

#### Lock document (EZ-DOC)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-DOC-1 | Parsing a rendered lock yields the packages, hub and tools that were rendered. | Proved | proved |
| EZ-DOC-2 | Packages are written in hash order and each package's files in path order, so the lock's text does not depend on the order the walk found them in. | Proved | proved |
| EZ-DOC-3 | `ez lock` output is a function of the ledger and the committed tree. A fresh clone reproduces the lock byte for byte. | Proved | proved |
| EZ-DOC-4 | `ez lock` is idempotent: run on the world it just produced, it writes the same bytes. | Proved | proved |
| EZ-DOC-5 | `ez lock` without `--upgrade` never writes ez.toml, and records every dependency's and tool's pin exactly as ez.toml has it. | Proved | proved |

EZ-DOC-2 replaces the draft's "rendering a parsed lock reproduces the original bytes". No code path re-renders a parsed lock, and the TOML renderer does no escaping, so that statement was about a function ez does not have. What the lock does guarantee is canonical order: `pack.sort` and `K.files_of` sorted before rendering, and `pack_ins_le` stated one step of it. WP3 proved the whole of it: the lock renders each package as one block filed under its hash and sorts the blocks with the same `K.file.sort` that EZ-HASH-1 rests on, so `lock_order_free` and `pack_order_free` follow from pkg's `sort_perm`. WP4 proved EZ-DOC-1 against the pinned eztoml v0.1.0 reader, with a file path holding `=` refused (see "Decided behavior changes").

EZ-DOC-3 is the headline guarantee of the whole tool, and it did not hold when we wrote it; the changes that make it hold were decided (see "What ez lock may read"), landed, and WP1 proved the row with `lock_reproducible` and `clone_reproduces`. The README says `root` and `narHash` exist so that `ez lock` never has to consult anything a clone does not have, and that part was true: plain lock copied them from the ledger and never recomputed them. But plain lock also read the untracked trees under `$BEND_LIB`, and when a non-vendored git dependency's tree was missing it wrote an empty `files` table and exited 0. On a fresh clone of this repository that happened to shake, eztoml and snap. As a law, EZ-DOC-3 is a frame property, and stating it forces us to define exactly what the lock may read:

```
# EZ-DOC-3
law lock_reproducible:
  for w1: World
  for w2: World
  for a: LockArgs
  for e: {inputs(w1) == inputs(w2) : Inputs}
  {Pair.fst(lock_plan(w1, a)) == Pair.fst(lock_plan(w2, a)) : List(Effect)}
```

`inputs` is a projection of the World, and defining it is itself part of the specification. If a future change makes `ez lock` read something outside it, this law stops proving, which is the regression we want to catch.

#### What ez lock may read

`inputs` is the ledger text, the committed `.bend` files as `git ls-files '*.bend'` lists them, the vendored trees under `.ez/lib`, and the files at each non-vendored git dependency's ledger rev. Hub content is not an input: it is addressed by hash and checked on arrival, so "the hub serves what was published" is a trust assumption (EZ-TRUST-3), and two worlds whose hubs both serve a hash serve the same bytes.

Tracing the command at `b28ca2c` showed what plain `ez lock` read, and each read outside that set was decided:

| Input at `b28ca2c` | Decision |
| :---- | :---- |
| untracked trees under `$BEND_LIB` for non-vendored git dependencies, with a missing tree written as `files = []` and exit 0 | Fetch the tree at the ledger's rev and check it against `narHash`. Refuse with exit 1 if either fails. Never write an empty `files` table for a git dependency. |
| `.ez/origins.toml` | Not read by `ez lock`. `ez add` already records every git dependency in the ledger. |
| every `*.bend` under the working directory, untracked files included | Walk `git ls-files '*.bend'` instead of `find`. |
| `BEND_HUB` for `[lock] hub` and for hub fetches | Take the hub from a `hub` key in the ledger's `[package]` table, defaulting to `https://hub.bend-lang.com`. |
| `bend version` for `[lock] bend` | Drop `[lock] bend` from the lock. The flake pins bend. |
| `git` and the network through `Pin.fill` when a tool pin lacks `rev` or `narHash`, writing ez.toml | Only under `--upgrade`. A plain lock with an incomplete tool pin refuses with exit 1. |

Every decision in this table has landed. Plain `ez lock` now reads the ledger, the files `git ls-files '*.bend'` lists, and one answer per package it asks about, and nothing else: the World in `lock/world.bend` has no field for the environment, the old lock, `.ez/origins.toml` or untracked files. Under `--upgrade` it also reads the remote's answers, `.gitignore` and the committed sources it may rewrite, all as questions the planner asks.

#### Resolution (EZ-RES)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-RES-1 | `ez add` with no ref pins the greatest semver-ish release tag on the remote; with no release, the greatest pre-release; with no semver-ish tag, the remote's default branch as its `HEAD` symref names it. A named ref resolves exactly, as `refs/tags/<ref>` and then `refs/heads/<ref>`. A 40-hex ref is used as a commit without asking the remote. | Proved | proved |
| EZ-RES-2 | `ez add` with no entry uses the revision's `[package] entry`, then `[package] bin`, then `main.bend`, and refuses if that file is not in the revision. An add that succeeds prints the import line for that entry's path inside the package, the line `ez publish` prints. `ez add <name>@<version>` with no entry uses the package's `main.bend`, then its first top-level `.bend` file, and records none when it has neither; it refuses an entry given that the package does not hold, and prints the import line with the name in place of the hash. | Proved | proved |
| EZ-RES-3 | A target containing `://` or starting `git@` is a git URL. A target starting `/`, `./`, `../` or `~/` is a path. A target of exactly two segments of letters, digits, `-`, `_` and `.`, neither of them `.` or `..`, is `https://github.com/<target>`, unless its second segment ends in `.bend`, which makes it a path. Anything else is a path, except the empty word, which is refused. For `ez add`, a path bend reads as a hub package's `<name>@<version>` names that package on the hub; a git URL, `owner/repo` or other path never does. | Proved | proved |
| EZ-RES-4 | `ez lock --upgrade` never moves a hub dependency. | Proved | proved |
| EZ-RES-5 | An upgraded rev-only dependency moves to the default branch tip only when its pin is an ancestor of that tip, and stays a commit pin. Otherwise the upgrade refuses with exit 1. | Proved | proved |
| EZ-RES-6 | `--package NAME` asks the remote to resolve only the named dependency or tool, and every other ledger entry keeps its rev, tag and hash. Resolving is asking for refs, the default branch, ancestry, or a checkout at a new rev. | Proved | proved |
| EZ-RES-7 | Tags, refs, and ancestry reported by git are accurate. | Trusted | |
| EZ-RES-8 | An upgraded tagged dependency re-resolves its tag. A tag that now names a commit the pin does not descend to, or a pinned commit whose tree no longer hashes to the pin, stops the upgrade with exit 1. | Proved | proved |

"Semver-ish" in EZ-RES-1 is what `git/git.bend` accepts: an optional `v` or `V`, one or more dot-separated numeric parts, an optional pre-release after `-`, and anything after `+` ignored. The comparator pads missing parts with zero. Three parts of EZ-RES-1 are decided changes: today a pre-release can beat an older release (`v2.0.0-rc1` over `v1.9.0`), the default branch is guessed as `main` then `master`, and names resolve with a tail-matching `ls-remote`, so `main` can resolve to `refs/heads/feature/main`. EZ-RES-1 and EZ-RES-2 are precedence rules, and each becomes a law over every list of tags or every manifest. When we wrote them they had no law at all, and `Git.latest` and `Git.default.ref` mixed the choice with the `ls-remote` calls. The choice is now a pure function of what `git ls-remote` printed, proved over any list of tags (`latest_greatest` rests on `ord.ver` being a total preorder), and `ez add` asks for that output through its planner, which proved both rows.

EZ-RES-6 is narrowed from the draft's "every other lock entry is unchanged", and says "resolve" because the lock that follows an upgrade still fetches every non-vendored git tree missing from BEND_LIB at its ledger rev, which asks the remote for a tree but resolves nothing. The final step of an upgrade recomputes the whole lock from the current world, so other entries are unchanged only when nothing else changed, which is EZ-DOC-3's job. What `--package` itself guarantees is about the ledger:

```
# EZ-RES-6
law upgrade_one_frames_others:
  for w: World
  for n: String
  for m: String
  for e: {String.eq(n, m) == False{} : Bool}
  {M.dep(upgrade_plan.ledger(w, n), m) == M.dep(M.parse(w.ledger), m) : M.Dep}
```

The law that landed is `lock/LAWS.bend upgrade_one_frames_deps`, with `upgrade_one_frames_tools` for the tools and `upgrade_one_asks_alone` for "asks the remote to resolve only the named dependency or tool": the questions an upgrade with `--package NAME` asks are exactly those it asks of a ledger holding nothing but the entries named `NAME`. [ez-lock-planner.md](ez-lock-planner.md) says where they differ from this sketch.

EZ-RES-8 is new. The code refuses on a moved tag and on drift, and closed laws (`tag_moved_off`, `same_rev_drifts`) showed the verdicts until the trails were deleted. In the dependency path the drift decision was made after the new tree had been laid, by `confirmed` in `ez/upgrade.bend`, and `U.judge` was called with its agreement bit fixed to true, so its `Drift` arm could not fire there. WP2 put the upgrade in the lock's planner, where a drifted pin is `U.judge`'s `Drift` and is refused before anything is laid, and WP6 proved the row.

EZ-RES-5 and EZ-RES-8 are proved relative to EZ-RES-7. The law says ez moves a pin only when the model's ancestry relation says so; whether that relation matches the real repository is git's responsibility.

#### Vendoring and source rewriting (EZ-VEN)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-VEN-1 | After `ez add`, `ez remove` or `ez lock --upgrade`, the `.gitignore` allowlist names exactly the hashes of dependencies marked `vendor = true`, and every other line of `.gitignore` is unchanged. | Proved | proved |
| EZ-VEN-2 | When an upgrade moves a hash, every line of a `.bend` file outside `.ez` and `.git` that starts `import <old>/` names `<new>` afterwards. | Proved | proved |
| EZ-VEN-3 | Import rewriting leaves every other line of every file byte-identical, and does not write a file with no matching line. | Proved | proved |
| EZ-VEN-4 | `ez doctor` never writes to the project's source files. | Proved | proved |
| EZ-VEN-5 | `ez doctor` reports every hash an import line names that the ledger does not, and every ledger dependency no import line names, and exits 1 when it reports any. | Proved | proved |
| EZ-VEN-6 | `ez doctor` reports a lock that `ez lock` would not write as it stands, judged without the network from the ledger, the committed sources and the trees under `BEND_LIB`, and exits 1 when it reports one or cannot judge it. | Proved | proved |

EZ-VEN-1 was not true when we wrote it: only `ez lock --upgrade` wrote the allowlist, `ez add` never wrote it, `ez remove` never removed a line, and `ez init` wrote `.ez/`, under which git ignores every allowlist line. The decided change derives the allowlist from the ledger with one pure function, `I.sync` in `manifest/ignore.bend`, which the three commands call, and changes `ez init` to write `.ez/*`, `!.ez/lib` and `.ez/lib/*`. The laws are stated over that function and over each command's plan, and the row is proved.

EZ-VEN-2 and EZ-VEN-3 together specify rewriting completely: the first says what changes, the second says nothing else does. The match is exact at column 0, so an indented import (which the package walk accepts) is not rewritten; the requirement states the column-0 rule so that a change to it is a behavior change. Swaps apply one after another, so the law quantifies over swap lists in which no move's new hash is a later move's old one (`moves.ok`; `SPEC.md` spells out the premise). A single closed example, `imports_follow_hash`, covered both requirements on one file until the trails were deleted; WP7 proved both rows over the text and over the upgrade's plan.

EZ-VEN-4 held when we wrote it (`ez/doctor.bend` had no file write) and was only provable because of the planner split, where it becomes a claim that the plan `doctor_plan` returns contains no effect under the project root. Every command used to run `Env.make()` first, which created `.ez`, `bin` and the library directory; we recorded that as accidental when we read the code, and it is fixed, so `ez doctor` creates nothing (`Env.dirs`, law `dirs_other`). EZ-VEN-5 is new; the drift report had six closed laws in `ez/LAWS.bend` (`report_both_ways` and the rest), deleted with the other trails, and no requirement until now. **Update (WP12):** `ez doctor` is in planner form (`doctor/world.bend`, `doctor/plan.bend`, `doctor/run.bend`), and EZ-VEN-4 and EZ-VEN-5 are proved over its plan; see "Update (WP12, `ez doctor`)" in [ez-add-planner.md](ez-add-planner.md). The plan is lines said and how the command ends, so doctor writes nothing at all (`doctor_writes_nothing`), which is stronger than the row asks. An import line is one the lock reads as one, so doctor and `ez lock` never disagree about what the source imports.

EZ-VEN-6 is new (WP19). Doctor checked that the lock parses and that the packages it records are under `BEND_LIB`, but not whether `ez lock` would write the same lock today, so a ledger whose pins had moved since the last lock passed. We check the lock the way `cargo --locked` and `uv lock --check` do, offline: doctor puts a plain `ez lock` to the lock's own planner, over the ledger, the sources git lists and the trees `BEND_LIB` holds, and compares the text it would write with ez.lock.toml byte for byte. So every hash, source, file sum and tool pin is checked by the code that writes it, rather than by a second reading of the lock that could drift from it. A hub package's tree under `BEND_LIB` is judged as the hub's bytes, since its name is the digest of its manifest and each file is checked against its sum. A package the lock planner asks about and `BEND_LIB` lacks is one doctor cannot see without the network, so the lock is then reported as not checked, not guessed at, and that fails the command, as `cargo --locked --offline` fails when it would need the network. A lock `ez lock` would refuse to write is reported the same way. The laws are over the check's line (`doctor_passes_fresh_lock`, `doctor_says_fresh_lock`, `doctor_reports_stale_lock`, `doctor_stale_lock_fails`, `doctor_unchecked_lock_fails`). Since the lock records the ledger's tool pins, the check reads them, and `doctor_ignores_tools` now says that the tools change nothing else doctor says.

#### Fetch (EZ-FETCH)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-FETCH-1 | `ez fetch` writes a package file under `BEND_LIB` only when its digest matches the lock: a hub body's digest starts with the lock's sum, a git file's digest equals it, and a git package's checkout weighs to the narHash the lock records. | Proved | proved |

This takes most of the weight off the draft's EZ-TRUST-3 ("the hub serves the tree whose hash was requested"). ez does not trust the hub's content: `Hub.judge` refuses a body that does not hash to what was asked for, and the three quantified `hub/judge_*` laws state the verdicts. What remains trusted is SHA-256 itself and the hub's availability. When we wrote the row, `ez fetch` did not check `narHash`, and it trusted a cached tree whose manifest text matched without re-reading its files. **Update (WP8):** `ez fetch` is in planner form (`fetch/plan.bend`), and EZ-FETCH-1 is proved by `fetch_lays_the_lock`, which asks of every file laid, hub or git, that its digest equal the lock's sum. A tree already under BEND_LIB is now read and checked like a fetched one before it is kept. `narHash` is still not checked: every file laid is checked against its own sum, and the package against its name, so the tree laid is the lock's whatever the checkout around it held. **Update (WP20):** it is now checked. A git package is laid only from a checkout that weighed to the lock's `narHash` (`fetch_lays_weighed`), so the checkout around the files is the one the lock pins.

#### Hub names (EZ-HUB)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-HUB-1 | A named import `<name>@<version>/...` resolves to one hash: the one ez.toml records for that name, else the one the lock being rewritten records, else the one the hub answers. The lock walks that package, records the pair under `[names]`, and `ez fetch` lays that hash in the name's file. `ez add <name>@<version>` asks the hub the ledger names, and records the name with the hash the hub answers. | Proved | proved |
| EZ-HUB-2 | `ez lock` asks the hub what a name names only when neither ez.toml nor the lock being rewritten records it. | Proved | proved |
| EZ-HUB-3 | An import whose first path segment holds `@` is a hub dependency and never a file of the project. A name bend would refuse is refused, in bend's words, before any package is hashed around it. | Proved | proved |
| EZ-HUB-4 | `ez lock` and `ez fetch` lay `BEND_LIB/names/<name>@<version>` holding the hash the lock records, for every name it records, and `ez add <name>@<version>` lays the file of the name it adds. `ez fetch` rewrites a file that names another hash, and says so. `ez doctor` fails when a file is missing or names another hash. | Proved | proved |

The group is new (WP23). Bend 2.0.26 reads `import <name>@<version>/file.bend as P` by looking in `BEND_LIB/names/<name>@<version>` for the `0x` hash the name stands for, and asks `GET $BEND_HUB/name/<name>@<version>` when that file is not there. A name is a moving part the hash is not, so we pin it the way cargo and uv pin a version to a checksum: the lock records each name with its hash under a `[names]` table, the package itself stays recorded by its hash as any hub package is, and the names file is laid from the lock so bend never asks the hub during a build. ez.toml records a named dependency as `[deps.<key>]` with `hub = "<name>@<version>"` beside its `hash`, and what ez.toml records wins over the lock and the hub. A name the lock already records is not asked again, so relocking needs no network for names, and `ez doctor` answers names from the lock and the files under `BEND_LIB` alone. That a name the hub answered once keeps its hash is trusted (EZ-TRUST-6), and the package the name gives is still checked against its hash like any other.

#### Tools (EZ-TOOL)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-TOOL-1 | The link directory is `$EZ_TOOL_BIN`, else `$XDG_BIN_HOME`, else `$HOME/.local/bin`, an empty value counting as unset. `ez tool install` and `ez tool upgrade` link there, and refuse before anything is built when all three are empty. | Proved | proved |
| EZ-TOOL-2 | A cached binary is reused only when the recorded commit, built file and bend version all equal the resolved ones, and never when the resolved commit is empty. A cached checkout is reused only when its recorded commit equals the resolved one. | Proved | proved |
| EZ-TOOL-3 | A local target with uncommitted or untracked changes, whatever the repository's own settings hide, or a path that is not the top of a checkout, resolves to no commit and is rebuilt on every run. | Proved | proved |
| EZ-TOOL-4 | A target naming a `[tools.*]` pin in ez.toml builds the lock's rev, url, entry and bin. An `owner/repo` or URL target builds the commit `git ls-remote <url> HEAD` names. A path builds its clean `HEAD`. A checkout with no ez.toml is a plain Bend repository: it is built with no lock fetched and with BEND_LIB at a library of its own under the cache, where bend fetches its hub imports. A checkout with an ez.toml and no ez.lock.toml is refused when its binary is to be built. | Proved | proved |
| EZ-TOOL-5 | `ez tool run` exits with the built program's status; any failure before the program runs exits 1. | Proved | proved |
| EZ-TOOL-6 | `ez tool install` and `ez tool upgrade` never run the built binary. | Proved | proved |
| EZ-TOOL-7 | The built file is the pin's `bin`, then the pin's `entry`, then the file `--entry` names, then the checkout's `bin`, then its `entry`, then `main.bend`, and a built file that is not in the checkout is refused. The link is named after the checkout's package name, or `app`; a plain repository's is the built file's name without `.bend`, or the repository's name when that is `main`; and a name that is not a TOML bare key is refused. | Proved | proved |
| EZ-TOOL-8 | A remote target whose cache slug is empty, absolute, or climbs with `..` is refused. | Proved | proved |
| EZ-TOOL-9 | `ez tool run [--entry <file>] <target>` passes every word after the target to the program, dropping one leading `--`. `ez run` passes every word after `run` to the entry ez.toml names, or `main.bend` when it names none. | Proved | proved |

EZ-TOOL-2 is a decided change. One file recorded only the commit, for both the checkout and the binary, so a pinned tool with an `entry` override and a free run of the same repo at the same rev could share a binary. The cache key now records the built file and the bend version, and the row is proved over that key (`key_*`, `checkout_*` in `ez/LAWS.bend`) and over the tool plan's reuse. EZ-TOOL-7, EZ-TOOL-8 and EZ-TOOL-9 are new; the closed laws for them in `ez/LAWS.bend` (`file_*`, `out_name*`, `target_escapes`, `argv_of_*`, `tool_rest_*`) were deleted with the other trails.

EZ-TOOL-5 is stated over the planner's outcome, not over a real process. The planner returns a run effect as its final effect after a successful build and exit 1 on every earlier failure; the interpreter passing the child's status through unchanged is covered by the interpreter trust assumption. Since WP16 the program runs on ez's own stdin, stdout and stderr, as `ez run`'s has since WP15, where it ran with stdin at `/dev/null` and its output held until it exited. How the program is started is interpreter behavior and not part of the requirement; the status it hands back is what the law is about. See "Decided behavior changes".

**Update (WP9):** the tool commands are in planner form (`tool/world.bend`, `tool/plan.bend`, `tool/run.bend`), and EZ-TOOL-1 and EZ-TOOL-3 to EZ-TOOL-9 are proved over the plan; see "Update (WP9, `ez tool`)" in [ez-add-planner.md](ez-add-planner.md). EZ-TOOL-1, EZ-TOOL-3 and EZ-TOOL-7 were reworded for the decided behavior changes below. The plan's last part is the program started or the link written, never both, so EZ-TOOL-5 and EZ-TOOL-6 are laws about that part.

#### Publish (EZ-PUB)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-PUB-1 | `ez publish` refuses, and sends nothing, when `git status --porcelain --untracked-files=normal` names any path, when git cannot answer it, or when a file of the package is one git does not track as unchanged (`git ls-files -v` tag `H`), an ignored file included. | Proved | proved |
| EZ-PUB-2 | `ez publish` succeeds only when bend exits 0, a line of its output is exactly a `0x` name, and every such line equals ez's own hash; it then prints that hash and the import line for the entry's path inside the package. Any other answer exits 1. | Proved | proved |

Both are new, and both are proved over the plan `ez publish` runs (`pub/plan.bend`), beside the decision functions they rest on (`clean_is_all_blank`, `unread_never_agrees`, `differs_never_agrees`, `ours_agrees`). EZ-PUB-2 describes the verdict, not the ordering, and the comparison runs after bend has uploaded. We looked for a way to compare first and found none: bend has no option that stops `--publish` between computing the hash and posting it (2.0.25 had none when we looked, and 2.0.27 has none either), and the only workaround, pointing `BEND_HUB` at a dead address and reading the hash from a progress line, depends on output bend does not promise and mines the proof of work twice. The check stays after the upload. EZ-PUB-2 promises that a disagreement exits 1 and prints no import line, not that nothing was sent.

### Outcomes and incidental output

Much of the brittleness in the closed laws ez had came from pinning whole outputs. The spec separates output into two kinds.

**Contractual output** is anything a user or a script can reasonably depend on: exit statuses, the bytes of files ez writes (lock, ledger, gitignore, rewritten imports), link paths, and effect plans. Requirements talk only about contractual output.

**Incidental output** is everything else, mainly human-readable progress and error wording. There is no consistent error format in ez today: failures are reported as `ez: <prose>`, `ez: <path>: ...`, `ez: git <subcmd>: ...`, `ez: error: ...`, Shake's unprefixed `error: ...`, or a subprocess's own output with no ez line at all. Planners should return a structured outcome and a separate renderer should turn it into text, so that laws are stated over the outcome and a change that rewords a message touches the renderer and no law. The one output rule the code does follow consistently is the exit status:

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-OUT-1 | Every command exits 0 on success and 1 on any failure ez detects, except `ez run` and `ez tool run`, which exit with the program's status. | Proved | proved |
| EZ-OUT-2 | A command that refuses writes nothing: every file it would otherwise write or remove is left as it found it. | Proved | proved |

EZ-OUT-2 is new, decided with the phase-three design. In planner form a command computes its whole plan before any effect runs, so a refusal is a plan with no write, lay or remove effect in it. It did not hold when we decided it: `ez lock --upgrade` wrote ez.toml, `.gitignore`, sources and trees in stages, and a failure in a later stage left the earlier writes in place. A write the interpreter attempts and the system rejects is not a refusal; that failure is EZ-OUT-1's, and what it leaves behind is covered by EZ-TRUST-2. Each command met EZ-OUT-2 when it was converted to planner form, and with `ez publish` (WP11) the row is proved for every command.

EZ-OUT-1 is proved over a pure function per command that gives its exit status (`P.status` of a plan's outcome, `TP.code` for the tool commands, the outcomes in `ez/ends.bend` for the commands that are not planners, and `ez/line.bend` for a line before any command runs); the interpreters only exit with it. `ez run` and `ez tool run` exit with the program's status, as `cargo run` does (`S.code` and `TP.code`), and 1 when they refuse before starting one.

EZ-OUT-1 replaces the draft's `ez: <area>:` prefix requirement, which the code does not implement. The 19 closed laws that pinned progress and error wording (`hub_404_teaches`, `drift_names_the_tag`, `installed_names_the_link` and the rest) pointed toward no requirement and were deleted in the first rollout phase.

### Retiring closed laws

Closed laws have no standing in this specification. They are not a level, they cannot carry a requirement tag, and nothing in the refactoring contract protects them. We retire them in two steps.

In the first rollout phase, every existing closed law is sorted against the requirement list, using the "points toward" column of the law-by-law inventory we kept while writing this revision. A closed law that illustrates a requirement is kept temporarily and marked with the ID it points toward, so the pending requirement has a visible trail. A closed law that fits no requirement is deleted, since it pins behavior nobody has decided to guarantee. By that inventory, 78 of the 122 closed laws are deleted in this step: the ones about the `ez test` runner, the CLI parser, progress and error wording, the spinner's terminal choice, and the SHA-256 and NAR vectors, whose requirements are Trusted. 43 point toward a Proved requirement and are kept, tagged, until its law lands. The remaining one, `dflt_https`, moves to ezhttp with the rest of `net/`. The thirteen refactor-equivalence laws are deleted in the same step, with the `old.*` definitions they compare against: the rewrites they checked have landed, and keeping the old definitions would maintain a second specification nobody reads.

The plan was to delete the closed laws pointing at a requirement in the same PR that lands its quantified law, which strictly subsumes them. We took the second step sooner. With 40 trails left and every pending row's real law already stated in an accepted design document (this RFC's requirement sections, and [ez-lock-planner.md](ez-lock-planner.md) for the lock), the trails were no longer telling anyone what to prove, and they held ez on an old bolt. We deleted all of them in one change, with their proofs and the sample values only they used. No closed law remains in ez.

bolt enforces the end state. Its `closed` rule flagged every law with no binder up to v0.4.0, but from v0.5.0 (bolt#10) it accepted a closed equality as a stated claim. At ez's request bolt v0.9.0 added `quantify` (L004), an opt-in rule that flagged every law with no binder unless the comment line right above it started with `# toward `, and ez ran it at `error` while the trails remained. bolt has since made `closed` (L002) strict itself: it flags every law in a LAWS.bend with no `for` or `exs` binder, equality or not, and nothing exempts one. L004 is retired. ez runs `closed` at `error`, so a new closed law cannot land.

### Tagging and traceability

Every quantified law that proves a requirement carries a comment naming it:

```
# EZ-RES-6
law upgrade_one_frames_others: ...
```

A check reads the requirement list and every LAWS.bend and fails when:

- A requirement at level Proved, marked proved, has an empty Law cell.
- A law a Proved row names, proved or pending, is missing, has no binder, or does not carry the row's ID.
- A law is tagged with an ID that the requirement list does not have as a Proved row.
- A requirement at level Trusted has a Law cell, or no row in the trust boundary table.

A pending row passes with an empty Law cell. `SPEC.md`'s pending statuses and its "Left to prove" section are the honest answer to "what does ez prove right now", and they shrink as proofs land.

Untagged quantified laws are allowed. ez has many of them: path lemmas, string lemmas, and the ledger reading laws that support EZ-LED. They pass the gate like any law, but the refactoring contract does not protect them, so a change may edit or delete them freely.

The check belongs in bolt, as a rule in the `laws` group next to `closed`, `coverage` (which bolt v0.9.0 called `law`) and `unsafe`, run through `mkLint`. It depends only on file contents, which keeps it inside the lint gate rather than adding a new runner. `SPEC.md` stays the single requirement list, and the rule parses only its requirement and trust table rows, so the document remains prose for people and a table for the check. ez's flake checks gain `mkLint` in the first rollout phase. bolt shipped the check as `trace` (L005, bolt#106, first released in bolt v1.2.0), opt-in: no group setting reaches it, and a project turns it on by naming it. ez's `bolt.bend` sets it to `error`, and `[tools.bolt]` pins bolt v1.2.1.

### Refactoring contract

This is the rule a contributor or an agent follows when changing ez's implementation. It is short on purpose.

A change to implementation code must keep every tagged law passing the proof gate without editing its statement in LAWS.bend. The proof in PROOF.bend may be rewritten freely, and untagged laws may be changed or removed.

A change may not move a requirement from Proved to Trusted. Weakening a guarantee is a behavior change and goes through review as one.

A change that adds a new Trusted row must justify it in the PR description, because every Trusted row is a place where the proof gate stops looking.

A change to a requirement in `SPEC.md` is a behavior change, not a refactor. It is the only way a tagged law's statement may change.

With this in place, "can I change this code and keep the proof?" has a mechanical answer: if the proof gate passes, no tagged statement changed, and the trust boundary did not grow, the change preserved every guarantee ez makes. No test run is required to establish that, and no agent claim that one is needed changes it.

### Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and naming them keeps the spec honest about what a passing proof gate means.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| EZ-TRUST-1 | The Bend checker is sound. | We cannot check it from inside Bend. The BendTT paper and a Lean formalization exist, and the release notes report mismatches between the formalization and the implementation. |
| EZ-TRUST-2 | The interpreter reads the World and executes plans faithfully. | It makes no decisions and is kept small enough to review line by line. |
| EZ-TRUST-3 | The hub serves, for a hash, what was published under it. | ez checks every hub body against the hash it asked for (EZ-FETCH-1), so this reduces to availability and EZ-HASH-6. |
| EZ-TRUST-4 | `ez prove` runs `bend` on every PROOF.bend in the tree and passes only on an exact `All terms check.` first line. | It is ez code run by `mkProofs`, not a law. CI builds from a clean tree, so nothing is cached. |
| EZ-TRUST-5 | HTTP framing and URL parsing are correct. | Proved in ezhttp v0.4.0, the rev ez.toml pins; ez's gate does not re-check it. |
| EZ-TRUST-6 | A `<name>@<version>` the hub answered once names the same hash forever. | The hub never moves a name once it is taken, so a name is resolved once and pinned in the lock. The package it names is still checked against its hash (EZ-FETCH-1). |
| EZ-RES-7 | git reports refs, tags, and ancestry accurately. | The World model takes git's answers as given. |
| EZ-HASH-4 | ez's 0x hash matches `bend --publish`. | The publisher is a separate program. |
| EZ-HASH-5 | ez's narHash matches nix. | nix is a separate program. What ez trusts of its own walk is GNU `find`'s listing of the tree, each path's type, `%M` mode, name and link target, and the file effect's read of each file's bytes. The walk takes the executable bit from the owner's exec bit of that mode, as nix's dumper does, and reads names and targets as listed (EZ-HASH-7). Submodules are not part of the tree: ez weighs a checkout without them, and its nix side asks `fetchgit` for the same. |
| EZ-HASH-6 | `Sha.raw` computes the SHA-256 digest of its bytes, and `Sha.hex` of its text's UTF-8. | Proved in Giulio2002/bend-sha256 against an executable FIPS 180-4 specification, at the hash ez vendors; ez's gate does not re-check it. Collision resistance is also assumed. |

EZ-TRUST-3 is narrowed from the first draft: ez verifies hub content itself (EZ-FETCH-1), so what remains is that the hub serves the hash at all, which is what lets EZ-DOC-3 leave hub content out of `inputs`.

### Decided behavior changes

Checking the draft against the code turned up places where the code and the intent disagree. A maintainer decided each one, and each lands as its own PR, separate from the spec's rollout. A requirement that depends on a change stays pending until the change lands.

For EZ-DOC-3, `ez lock` stops reading anything outside `inputs`. It fetches each non-vendored git dependency at its ledger rev and checks it against `narHash`, refusing on failure instead of writing an empty `files` table. It stops reading `.ez/origins.toml`. It walks `git ls-files '*.bend'` instead of `find`. It takes the hub from a `hub` key in the ledger's `[package]` table, with a constant default, instead of `BEND_HUB`. It drops `[lock] bend` from the lock. And it fills an incomplete tool pin only under `--upgrade`, refusing otherwise.

The phase-three design ([ez-lock-planner.md](ez-lock-planner.md)) adds five more for `ez lock`. It takes the hub imports of every tracked `.bend` file and follows no local import, so an untracked file a tracked one imports never reaches the lock. It checks every package's manifest against its `0x` name, a tree already under `BEND_LIB` included, and judges such a tree as the same bytes cloned at the ledger rev and weighed to the ledger's `narHash`. It refuses to write a lock that is not `lockable`, one with a key or value holding `"`, `\` or a newline, since the TOML renderer does no escaping, or with a file path holding `=` (below). `ez lock --upgrade` stops writing `.ez/origins.toml`, which nothing reads. And an upgrade lays a moved vendored dependency's tree under `.ez/lib`, where it is committed, and any other moved tree under `$BEND_LIB`, as a cache fill.

The design for `ez add` and `ez remove` ([ez-add-planner.md](ez-add-planner.md)) adds seven more. A refused `ez add` lays nothing, where it used to leave the fetched tree under `$BEND_LIB`. `ez add` stops writing `.ez/origins.toml`. Re-adding a `vendor = true` dependency lays its tree under `.ez/lib`, where it is committed, and drops the old committed tree when the hash moved. `ez remove` of a vendored dependency drops its committed tree, unless another dependency in the ledger still names that hash. `ez remove` of a name the ledger does not have refuses with exit 1 and writes nothing, where it used to rewrite the ledger and exit 0. A package whose imports climb out of the checkout it was fetched into is refused, where its hash used to depend on the directories above that checkout. And ez writes `vendor = true` as a bare TOML boolean rather than the string `"true"`, reading either spelling.

For EZ-DOC-1, `ez lock` refuses a package with a file whose path holds `=`, naming the package and the path, and writes nothing. A path is written as a quoted key, and the pinned eztoml v0.1.0 reader cuts a pair line at its first `=` even inside a quoted key ([eztoml#24](https://github.com/Emerging-Patterns/eztoml/issues/24), closed: v0.1.0 is not patched, and 0.2.x, a real TOML lexer, keeps the `=`). Before the refusal, such a path was written into a lock that `ez fetch` read back as a different path and could not restore. The refusal lifts when ez moves to eztoml 0.2.x (see "Rollout").

For EZ-LED-4, every command that writes ez.toml refuses, with exit 1 and nothing written, a ledger that would not read back as the model it rendered: one with a name or value holding `"`, `\` or a newline, a dependency with no hash, or a git source that names no repo or no root. `ez init 'my"app'` wrote `name = "my"app"`, which TOML cannot read, and `ez remove` rewrote a hand-edited `entry = "src\main.bend"` as it was, which eztoml v0.1.0 reads back and a TOML reader such as nix's does not; both now refuse. The pinned reader does no escaping, so we refuse what it cannot carry, as the lock does (`lockable`), rather than write a file that means something else to another reader. The last two cases cannot come from a ledger that was read, since the reader asks every dependency for a hash and fills an absent `root`, so the refusal meets only values a user typed or edited in.

For EZ-RES-1, a release tag beats any pre-release, the default branch is the remote's `HEAD` symref rather than a guess of `main` then `master`, and a named ref resolves exactly, as `refs/tags/<ref>` and then `refs/heads/<ref>`.

For EZ-RES-3, `owner/repo` allows `.` in both segments, and a second segment ending in `.bend` makes the target a path, so `vercel/next.js` is GitHub and `src/main.bend` is a path.

For EZ-VEN-1, one pure function derives the gitignore allowlist from the ledger, and `ez add`, `ez remove` and `ez lock --upgrade` call it. `ez init` writes `.ez/*`, `!.ez/lib` and `.ez/lib/*` instead of `.ez/`.

Three more for EZ-VEN, found while proving WP7 of the phase-three design and shown on the binary first. The allowlist names each vendored hash once, where the ledger first names it: two dependencies that share a tree (one repository at one rev, under two names) wrote its `!.ez/lib/<hash>` line twice, and cargo and uv dedupe such entries. A `.gitignore` is its lines, each ending with a newline, so a file of a blank line and a stale allowlist line keeps its blank line; it was written empty. And an upgrade rewrites only a line that starts `import <old>/`, as EZ-VEN-2 says; it also rewrote `import <old>` with nothing after the hash, which EZ-VEN-3 forbids.

For EZ-TOOL-2, the tool cache records the built file and the bend version beside the commit.

For EZ-PUB-2, nothing changes. bend 2.0.27 cannot report a package's hash without uploading, so the check stays after the upload.

For EZ-HASH-4, the package walk follows bend 2.0.27, which changed what a package holds. `bend --publish` now takes along every file named exactly `LICENSE` beside a file it publishes, at the same path, and the hash covers it; it refuses a file under a directory named license in any case, since that clashes with a `LICENSE` on a disk that ignores case. The hub shows the license from the shallowest `LICENSE`'s `SPDX-License-Identifier` line, and a package with no `LICENSE` is MIT-0 under BendHub's terms, which bend warns about on every such publish. ez's walk takes the same files and makes the same refusal, so `ez add` names a git package as bend 2.0.27 would publish it and `ez publish` agrees with the hash bend mines; before, a package with a `LICENSE` beside a source was named without it, and `ez publish` uploaded it and then refused the disagreement. A pin written before names the same checkout without its `LICENSE` files, and those bytes are still the package that name is the digest of, so `ez lock` and `ez lock --upgrade` take a checkout whose walked manifest does not hash to the pin without its `LICENSE` files, rather than refusing a ledger that locked before. We follow the name here as cargo and uv follow the checksum they recorded: the lock keeps what the ledger pinned, and only a new `ez add` takes the new rule. A hub package is never walked, so an already published hash is unaffected. None of ez's own dependencies has a `LICENSE` beside a file it publishes, and ez.lock.toml does not change.

For the proof gate, a new `ez prove` command runs `bend` on every PROOF.bend and applies the exact `All terms check.` rule, and `mkProofs` runs it instead of `ez test`.

For EZ-LED-6 to EZ-LED-8, `ez init` refuses a directory that already has a ledger, and `ez add`, `ez remove` and `ez lock` refuse one that has none. `ez add` names a dependency the way cargo does, by the package's own `[package] name` first, with `--rename` to override it, instead of after its entry file, where two `main.bend` entries collided; a name the ledger gives another source is refused, and re-adding a dependency keeps its `vendor = true`. A relative path target is recorded as given and resolved against the project root wherever git reads it, where `ez add` had fetched it relative to a work directory.

Converting `ez fetch` to planner form (WP8) adds six more, each shown on the binary first against local git upstreams and a `file://` hub. With no ez.toml, or with ez.toml and no ez.lock.toml, `ez fetch` refuses with exit 1 and asks nothing, where it read a missing lock as empty and exited 0. We follow `uv sync --frozen` here rather than `cargo fetch`, which writes a lock when there is none: a fetch resolves nothing, so writing a lock would make it a second `ez lock`, and EZ-FETCH-1 has no lock to check against. A refused fetch writes nothing, where a file that did not match removed the tree already under BEND_LIB before it was checked, left a `.work-<hash>` clone under BEND_LIB, and kept the packages laid before it. A package whose files do not hash to the name the lock records them under is refused, where it was laid under that name (EZ-HASH-3). A file path in the lock that climbs out with `..`, is absolute or is not written the way the walk writes it is refused, where it was written outside BEND_LIB. A tree already under BEND_LIB is read and checked like a fetched one before it is kept, where a matching manifest was trusted without its files. And a tool's lock is fetched with its relative paths read from the tool's checkout, where they were read from the directory `ez tool` ran in.

Converting the tool commands to planner form (WP9) adds eight more, each shown on the binary first against local git upstreams, and each decided as cargo and uv would. A tool command that refuses leaves nothing behind: a remote with no ez.toml, or one whose package name ez refuses, left its clone and its record under the cache, and an install with nowhere to link built the binary before it refused; every refusal is now decided before anything is written, as `cargo install` builds in a directory it removes when the build fails. A path that is not the top of its checkout is no commit: a tool in a directory the enclosing repository ignores was cached under that repository's HEAD and ran stale after an edit. `git status` is asked with `--untracked-files=normal`, as for EZ-PUB-1, so a repository that sets `status.showUntrackedFiles=no` no longer passes for clean with an untracked file the build reads. Every binary lives in a directory named by its record, and a remote's checkout in a directory named by its commit, as cargo keeps one checkout per commit under `~/.cargo/git/checkouts`; a pinned `ez tool run` at another commit used to rebuild in place the binary an earlier `ez tool install` of the same repository linked, so the installed command silently changed version, and now both are kept. A package name that is not a TOML bare key is refused, as cargo refuses an invalid package name; `name = "../../evil"` wrote the binary outside the cache and would have linked outside the link directory. A pin whose rev is not a 40-hex commit is refused before anything is asked, since the rev names a directory. A URL with no host, `file:///srv/repo`, is cached where `file://localhost/srv/repo` is, where it was refused for an absolute slug. And `ez tool sync` checks every pin against the lock before it installs any, where it installed the pins before a missing one and then refused; a sync that goes on installs each pin in turn, and a later refusal leaves the earlier ones installed, as `cargo install a b` does.

Proving the `ez lock` halves of EZ-LED-8, EZ-HASH-3 and EZ-VEN-1 (WP10) adds one, shown on the binary first against a local git upstream. A package whose manifest hashes to its name, and whose files match their sums, but whose manifest does not list its files the way the name is taken (one line per file, in path order, each once) is refused by `ez lock`, where it was locked: a tree under BEND_LIB whose manifest listed two files in reverse order under the name of that text locked with exit 0, and `ez fetch` from that lock into an empty BEND_LIB then refused the package, since its files do not hash to the name. The lock now makes the check `ez fetch` makes, as cargo and uv check a package against the checksum their lock records when they write the lock, not first when they install from it. The lock also names a relative path source by its anchored path in the lines it prints while it fetches, as `ez add` and `ez fetch` already did, since git is now asked the source the planner anchored.

Converting `ez publish` to planner form (WP11) adds five more, each shown on the binary first with a stand-in `bend` that uploads nothing, and each decided as cargo and uv would. With no ez.toml, or one that does not parse, `ez publish` refuses and sends nothing, where it walked `main.bend` as if the ledger had named it, as `cargo publish` refuses a directory with no Cargo.toml. A file of the package that git does not track is refused before the upload, where an ignored file the entry imports, or a whole project in a directory the enclosing repository ignores, passed `git status` and was sent though no commit held it; `cargo publish` packages only what git holds, and since bend decides the file set we refuse instead. A file marked `--assume-unchanged` or `--skip-worktree` counts as untracked, since `git status` does not report its changes. bend's output agrees only when every line of it that is a `0x` name is ez's hash, where the first such line was taken and a second, different one was ignored. And the import line names the entry's path inside the package, `import <hash>/app/lib.bend as Lib` for a package that climbs out of `src/app`, which is the line bend prints; ez printed the entry's name alone, a path the hub does not serve. We kept the status check over the whole repository rather than narrowing it to the project's directory, as cargo does: a change beside the project refuses a publish that would not have sent it, which costs a commit and never a wrong package.

Converting `ez doctor` to planner form (WP12) adds five more, each shown on the binary first against a project with local git dependencies, one of them vendored, and a `[tools.*]` pin, and each decided as `cargo check` would. Doctor reads the import lines `ez lock` reads, the header imports of every `.bend` file git tracks outside `.ez/`, as the package walk scans them: an indented import, which bend accepts and the lock follows, was not seen, so its dependency was reported as one no import line uses; an import in a file git does not track was reported although the lock never records it; and `import 0x2222 as Q`, which names no hub package, was reported as the hash `0x2222 as Q`. With no ez.toml, doctor fails, as `cargo check` fails outside a package, where it passed with the line `ez.toml: , entry , 0 dependencies`; and with a ledger that does not read, it compares nothing, where it reported every import as missing from an empty ledger. The lock is read as TOML: a lock that is there and does not parse fails doctor whether or not the ledger has dependencies, as cargo refuses a Cargo.lock it cannot read, where it passed a project with none; and the packages it counts and looks for under BEND_LIB are the ones it records, where every `0x` hash anywhere in the file counted, a file path holding one included.

Closing the stale-lock gap (WP19) adds one, shown on the binary first in this repository: with ez.toml's `[tools.bolt]` tag moved from `v1.3.4` to `v1.3.5` and no relock, or with a git rev in ez.lock.toml edited by hand, `ez doctor` passed with exit 0, and now says `ez.lock.toml: out of date with ez.toml and the sources; run ez lock` and exits 1 (EZ-VEN-6). With `BEND_LIB` empty it says which packages it could not see and exits 1, as it already did for the missing packages themselves.

Proving EZ-OUT-1 (WP13) adds three, each shown on the binary first against local git upstreams, with a stand-in `bend` for publish, and each decided as cargo would. With no ez.toml, `ez tool sync` refuses and exits 1, where it synced nothing and exited 0, as `ez lock` and `ez fetch` refuse a directory with no ledger and cargo refuses one with no Cargo.toml. A bare `ez tool` prints the help of `ez tool` on stderr and exits 1, where it printed the help of `ez` on stdout and exited 0: a bare `ez` is help, as a bare `cargo` is, but a group that was not told which of its commands to run is a line that did not say what it wanted, as `cargo report` with no command is. And `ez help` of a word that names no command, `ez help bogus`, fails with the error `ez bogus` gets and exits 1, where it printed the help of `ez` and exited 0, as `cargo help bogus` fails. Every other command already exited 0 on success and 1 on a failure ez detects, and `ez tool run` with the program's status, so nothing else changed on the binary; what changed is where the status comes from. Each command's status is now computed by a pure function the laws are about (`P.status` of a plan's outcome, `TP.code` for the tool commands, the outcomes in `ez/ends.bend` for the commands that are not planners, and `L.status` for the line before any command runs), and the interpreters only exit with it. We kept `ez run` exiting 1 when the program fails, rather than with the program's status as `cargo run` does, since EZ-OUT-1 names `ez tool run` as its only exception.

Making `ez run` behave as `cargo run` and `uv run` do (WP15) adds four, each shown on the binary first in a scratch project, and each decided as cargo would. `ez run` hands the program ez's own stdin, stdout and stderr, where it ran bend with stdin at `/dev/null` and printed what bend said only once bend had exited: a program that prints a line a second showed all three lines together after three seconds, and now shows each as it is printed, and a program that reads stdin read nothing, and now reads what was piped to `ez run`. `ez run` exits with the program's status, where it exited 1 for any status but 0: a program that ends with `IO.die` and status 7 exited 1, and now exits 7, and a program bend refuses to check still exits with bend's status, 1. With no ez.toml, `ez run` refuses and exits 1 with `ez: no ez.toml here; ez run runs a project's entry, and ez init makes one`, where it ran `main.bend` and exited 0, as `cargo run` refuses a directory with no Cargo.toml; with an ez.toml that does not parse, it refuses with the parse error, where it also fell back to `main.bend`. `ez check` and `ez build` had the same silent fallback, `ez build` naming its binary `bin/app.out` for want of a package name, and refuse the same way, as `cargo check` and `cargo build` do; a refused check or build makes neither `.ez` nor `bin`, where both were made before the ledger was read. Each decision is a pure function of ez.toml's text and the words given (`S.start` in `ez/start.bend`), and `ez run`'s status is `S.code` of that decision and the program's status; that the interpreter runs the line with the project's BEND_LIB in front of it and hands the status back is EZ-TRUST-2. Base has no effect that starts a program on the caller's own stdio, and snap's `exec` captures what it runs, so `ez run` starts bend through a small effect of ez's own, `ez/pass.bend`, the one foreign body in ez's tree. `ez build` keeps its status of 0 or 1, since the binary it makes is not run.

Making `ez tool run` behave as `cargo run` does (WP16) adds two, each shown on the binary first against a local git upstream whose program prints a line a second, reads stdin and ends with `IO.die` and status 7, and each decided as cargo would. `ez tool run` starts the built program on ez's own stdin, stdout and stderr through `Pass.run`, the effect `ez run` has used since WP15, where it ran the program through snap's `exec`, with stdin at `/dev/null` and what it printed held until it exited: the three lines came out together after three seconds, and now each comes out as it is printed; the program read nothing, and now reads what was piped to `ez tool run`; and what the program wrote to stderr reached ez's stdout, and now reaches ez's stderr. The status was already the program's and still is: 7 for the `IO.die`, and 143 for a program killed by SIGTERM, 128 plus the signal. `Pass.run` always answers a number, 127 for a program that cannot be started, so the interpreter no longer reads a status that is not a number as 1, and `TP.program`, which did that, is gone. Everything before the program starts stays on its path: the fetch, the build, the cache and the record. The build stays captured, since cargo shows its progress and not the compiler's chatter, and bend's output is shown only when the build fails. That output, and the warning that nothing caps `bend`, now go to stderr, where both went to stdout, since stdout is the program's and cargo keeps its own words off it. The warning moves to stderr for `ez tool install` and `ez tool upgrade` too, which otherwise print what they printed; `ez build`, `ez test` and `ez prove` keep it on stdout. The plan, its exit type and the laws are unchanged: `tool_run_exits_with_program` and `tool_run_status_is_program` still hold of the plan, and that the interpreter starts the program last and hands its status to `TP.code` is EZ-TRUST-2.

Proving what `ez add` prints (WP17) adds one, shown on the binary first against a local git upstream whose entry `src/says.bend` imports `../x.bend`. `ez add` prints the import line for the entry's path inside the package, `import <hash>/src/says.bend as Says`, where it printed the entry's name alone, `import <hash>/says.bend as Says`, a path neither BEND_LIB nor the hub holds, so bend went to the hub for it and a file holding that line did not check. The line is now the one `ez publish` has printed since WP11 and the one bend prints: both commands call `Git.import.line` on the entry's path inside the package, `K.inside` of the walk's root and the entry. A package whose imports stay inside the entry's directory prints what it printed, since its root is that directory. The ledger and lock `ez add` writes were already right and are unchanged.

Reading import lines as bend 2.0.25 reads them (WP18) adds three, each decided by what bend 2.0.25's loader and parser do, and the first two shown on the binary first against a local path dependency: `book_load` trims each header line and splits an import on `\s+`. The scan that `ez lock`, `ez doctor` and the package walk share cuts a line at any run of JavaScript white space, tabs and the Unicode spaces included, and trims it the same way, where it split on spaces alone: `import<TAB>0x…/lib.bend as L`, which bend runs, was missing from the lock and reported unused by doctor. `import Base # note` keeps the header open, as bend reads it, where the comment ended the header and every import below it was dropped. And a foreign body is `import`, then any run of spaces, tabs and carriage returns, then a quoted path, as bend's parser skips them, where exactly one space was read. The rewriter an upgrade runs stays narrower on purpose: EZ-VEN-2 and EZ-VEN-3 promise a byte-exact rewrite of the lines that start `import <old>/` at column 0, so an indented or tab-separated import keeps its old hash, and doctor then reports that hash as one the ledger does not name.

Closing the NAR gaps (WP20) adds four, each shown on the binary first against `nix hash path --sri` from a static nix 2.x build, and each decided as nix, cargo and uv would. The NAR walk takes a file's executable bit from the owner's exec bit of its mode, as nix's dumper does (`S_IXUSR`), where it asked `test -x`: run as root, files with modes `654` and `055` were executable to ez and not to nix, so their trees hashed differently from nix, and a file someone else owns, weighed by a user the mode does not let execute it, was the other way round. It reads a name and a symlink target as they are, where it trimmed `find`'s output and each target: a symlink to ` target ` hashed as one to `target`. It lists the whole tree once, `find` printing each field ended by a NUL, and reads each file by its path through the file effect, where it listed each directory with one name per line and handed each path to `test` and `readlink` as an argument, which the process effect separates by newlines: a name with a leading space, and a name holding a newline, made the walk stop with `not a file, directory, or symlink`, and a tree holding either could not be locked at all. On a tree with an executable file, both modes, a symlink, a spaced target, a leading and a trailing space, a newline and a non-ASCII name, ez and nix now print the same narHash, as they do for the pinned eztoml and ezhttp checkouts and for ez's own tree; the walk also runs one program per tree where it ran four per path. `ez fetch` checks a git package's checkout against the lock's `narHash` before it lays anything, and refuses with both hashes when they differ, where it laid the package whenever its files matched their sums: a lock whose `narHash` had been edited to another tree's fetched with exit 0 and laid the package, and now exits 1 and lays nothing. The check is the one `ez lock` already made, so a lock `ez lock` wrote fetches as before; it makes `ez fetch` refuse what the nix build of the same lock refuses, since `fetchgit` checks the same `narHash`. Cargo and uv pin a git dependency by its commit alone, which names the tree only as far as git's SHA-1 does; the lock records `narHash` for nix, so `ez fetch` holds the checkout to it too. And ez does not fetch submodules: it weighs a checkout without them, and its nix side now asks `fetchgit` for `fetchSubmodules = false`, where nixpkgs' default of `true` would have hashed a repository with submodules differently from the lock. Cargo fetches submodules for git dependencies because a crate's build script may compile the C sources a submodule holds. A Bend package has no build script, and every file it imports is recorded in the lock with its sum, so a file in a submodule is either another package, which ez records from its own repository, or a file the lock could not have pinned. We keep the checkout to the repository at the pinned commit, as `builtins.fetchGit` does by default.

Reading named imports (WP23) adds one, shown on the binary first against a local fake hub that answers `/name/` and serves one package. A project whose `main.bend` imported `<name>@<version>/lib.bend` locked with exit 0 to a lock that named no package, since the import scan followed only `0x` names, so a fresh clone had nothing to fetch and bend went to the hub for the name and the package at build time. `ez lock` now resolves the name, walks the package it names, records the pair under `[names]` and lays the names file; `ez fetch` on a fresh clone lays the package and the names file, and bend builds with `BEND_HUB` pointed at a port nothing listens on. A named import in the project's own files has to be an ez.toml dependency, and `ez lock` refuses one that is not rather than asking the hub for a name no one recorded. `ez lock --upgrade` leaves named dependencies as they are, and rewriting import lines stays about `0x` hashes: moving a name to another version is a choice of the project's, not a newer commit.

Adding a named hub dependency (WP24) adds one, shown on the binary first against a local fake hub that answers `/name/` and serves the package. `ez add <name>@<version>` read the word as a path, since it holds no `/` and no `://`, and git refused it as a repository that is not there; ez.toml got a named dependency only by hand. A word bend reads as a hub package's name, by its NAMED rule, is now that package: `ez add` asks the hub the ledger names what the name names, fetches that package's manifest and files from the hub, and judges them as `ez lock` judges a hub package, so a manifest that does not hash to the name the hub answered is refused. It lays the tree under BEND_LIB and the name's file beside it, so bend builds at once without asking the hub, records `[deps.<key>]` with `hub = "<name>@<version>"` and `hash`, and prints the hash and `import <name>@<version>/<entry> as <Entry>`, the line `ez publish` prints with the name in place of the hash. Only a word `classify` already reads as a path is asked whether it is a name, so a git URL, `git@host:path` and `owner/repo` are what they were. We decided four things as cargo and uv would. The key is `--rename`, else the key the ledger already gives a dependency added by the same name part, else the name part: adding another version of a name replaces the entry, as `cargo add foo@2` replaces `foo = "1"` and as re-adding a git dependency at a new tag does, and a key the ledger gives any other dependency is refused rather than written over. The word after the name is the entry, since a name pins its version and takes no ref; giving both a ref and an entry is refused. With no entry, the entry is the package's `main.bend`, else its first top-level `.bend` file in manifest order, which is the file `ez publish` walked from when the package was published by one, else none, and an add with no entry says the hash and prints no import line; an entry given that the package does not hold is refused. And `ez add` still writes no lock, for a name as for a git package, as `cargo add` leaves `Cargo.lock` to the next build: the next `ez lock` reads the name and its hash from ez.toml and puts nothing to the hub (EZ-HUB-2).

Publishing by name (WP25) adds one, shown on the binary first with a stand-in `bend` that logs its arguments and uploads nothing. `ez publish` ran `bend <entry> --publish` whatever the ledger said, so a package could go on the hub by name only through bend by hand. The ledger's `[package]` table now takes two keys, `publish-as`, the hub name, and `version`, and with both `ez publish` runs `bend <entry> --publish <publish-as>@<version>.0` and prints the import line by that name after the hash (EZ-PUB-3). We took a new key for the name rather than `name`, which a ledger may already hold as anything and which `ez add` reads as a dependency's key, and rather than `hub`, which is the hub's URL, as cargo keeps a registry's name apart from the package's. The version is `MAJOR.MINOR.PATCH`, as cargo and uv write one, and ez adds bend's fourth number as `.0`; a pre-release or build suffix is refused, since bend's four numbers have no way to write one, and we would rather refuse than drop it. One key without the other is refused before git is asked or bend is run, naming the key that is missing, as `cargo publish` refuses a package with no version; with neither, `ez publish` publishes by hash as before. `ez init` writes neither key. Both keys are in the ledger model, so `ez add`, `ez remove` and `ez lock --upgrade` keep them when they rewrite ez.toml, since a rewrite keeps the keys the model holds and drops any other, and `Rend.renderable` checks them so the ledger still reads back (EZ-LED-4).

Laying out a new project and showing its hub description (WP26) adds two, shown on the binary first, the upload with a stand-in `bend` that logs its arguments and uploads nothing. `ez init` wrote ez.toml, `.gitignore` and a `main.bend` that opened with `import Base`, and the hub describes a package by the first line of its first file by path, in plain string order and passing over `LICENSE`, so it listed every such package as `import Base`. `ez init` now takes `--description`, and the entry it writes opens with `# <name>: <description>`, or with `# <name>: TODO describe <name>` when none is given, a placeholder that says what is missing where the author will see it. A description holding a newline is refused, since it would spill into the program. cargo writes no description into a new Cargo.toml and asks for one only when a package is published; the hub has no field for one, so ours goes where the hub reads it. `ez init` also lays the project out as `cargo new` does, the program at the top and a library under `src/`: `src/lib.bend` holds `greeting`, which the entry imports and prints, so `ez run` on a fresh project prints `hello` as it did. git keeps no empty directory, so `src/` holds a file rather than a `.gitkeep`, and we named it `lib.bend`, as cargo names `src/lib.rs`, rather than after the package, since a package name need not be a name bend's import line can carry. In the package that entry makes, `main.bend` comes before `src/lib.bend`, so the hub shows the entry's first line. The library is laid out only with a stub at the project's top, where `./src/lib.bend` finds it; an entry asked for in a directory of its own is written alone, and an entry or a `src/lib.bend` that is already there is never written over. The layout is only what `ez init` writes for a new project: other layouts, such as ez's own `manifest/manifest.bend` entry, keep working, and `ez doctor` does not check it. `ez publish`, once every check before the upload has passed and just before bend runs, prints `hub description: <line>`, the line the hub will show, picked as the hub picks it from the files the walk made, which are the files bend sends. It goes to stderr, where bend's own notices go, so stdout stays the hash and the import line, and a publish refused before the upload prints only why. bend cannot be stopped between that line and the upload, so the line is for the author to read while bend mines its proof of work, not a question it waits on.

Running a plain Bend repository as `uvx` runs any package (WP28) adds five, each shown on the binary first against a local repository with no ez.toml and a local ez project, and each decided as uv and cargo would. A checkout with no ez.toml is a plain Bend repository, which `ez tool run`, `install` and `upgrade` refused (`<path> has no ez.toml`): it now builds `main.bend`, or the file a new `--entry <path.bend>` names, with no lock fetched and with BEND_LIB at `<slug>/lib` under the cache, beside the binaries, so bend fetches the program's hub imports itself and checks each against its name, as `uvx` runs a package that is not a uv project. `--entry` wins over a checkout's `bin` and `entry`, as cargo's `--bin` does, and not over a `[tools.*]` pin's, which the project decided; on `ez tool run` it comes before the target, as uvx takes its own options before the command, so every word after the target is still the program's. A plain repository is linked under the built file's name without `.bend`, or, when that is `main`, under the repository's name, the last segment of its URL or path with `.git` dropped. A built file that is not in the checkout is refused before anything is written, with a message that names it and suggests `--entry`, where a missing entry reached bend and failed there. And a cached remote checkout is reused whenever its record names the commit, where it was also asked to hold an ez.toml. A checkout with an ez.toml and no ez.lock.toml is still refused, now saying that its author runs `ez lock`, since a project built without its lock would take its git dependencies as they are today.

Refusing a package whose hub imports are not on the hub (WP30) adds one, shown on the binary first against a local fake hub and a stand-in `bend` that logs its arguments and uploads nothing. `ez publish` sent a package whatever it imported, so a package importing `0x<hash>/...` for a dependency that lives only in git, or a `<name>@<version>` the hub does not know, went on the hub and no one could build it from there: bend fetches every hub import from the hub. Past the check that git tracks every file, and before the hub description and the upload, `ez publish` now collects every hub import of the package's files, the entry, what it imports and the `LICENSE` beside each, each `0x` name and each name once, and asks the hub the ledger names about each, with the requests `ez lock` already makes: `GET <hub>/<hash>/manifest`, whose body must hash to the name, and `GET <hub>/name/<nv>`, which must answer a `0x` name, the one the lock's `[names]` or the ledger resolved it to when either records one. When a name is imported it reads ez.lock.toml first. If any is missing it refuses with exit 1, sends nothing and writes nothing, naming every missing import and, when the ledger records it, the dependency's key and origin, as in `0x04b9... (eztoml, git https://github.com/Emerging-Patterns/eztoml) is not on the hub; publish it first` (EZ-PUB-5, EZ-OUT-2). This is `cargo publish`, which refuses a dependency that is not on crates.io. We decided three things. A hub that cannot be asked, unreachable or answering anything but 200 or 404, refuses too, since what cannot be checked is not sent on a guess, as `cargo publish` fails when it cannot reach the registry's index. Every import is asked before any is judged, so one refusal names them all rather than the first. And the hub asked is the one the ledger names, the hub `ez lock` resolved the imports against, while bend uploads to `BEND_HUB` as it always has; the two are bend's own hub unless a project sets one of them, and a project that publishes to another hub names it in both places. A package with no hub import asks the hub nothing and publishes as before.

Moving to shake v0.2.0, snap v1.0.0 and the published sha256 package (WP31) adds four, each shown on the binary first against the v1.0.0 build. ez now imports only shake's interface, `main.bend`, and takes what shake proves as trusted (EZ-TRUST-7) rather than reading its types apart: the line laws are stated over `help_path`, `path_of` and `at`. A usage error names the command it happened in, as clap does: `ez lock --bogus` shows `Usage: ez lock [OPTIONS]` where it showed `Usage: ez [COMMAND]` (SHAKE-ERR-2). An option given twice is refused, as clap refuses one not declared to repeat: `ez lock --package x --package y` exits 1 with "the argument 'package' cannot be used multiple times", where the last value won (SHAKE-PARSE-10). A command reads only the bindings made while it was current, so the line hands a command the Matched at the end of the selected path (`L.leaf`); no command of ez has a flag of its parent, so no line binds differently. `ez help bogus` still exits 1, now because shake refuses it as `Unexpected` (SHAKE-PARSE-8) rather than because ez looked the path up itself, and `ez help` of a real path still exits 0. The `ez sync` hint is given when the first word is `sync`, where it was given when shake refused any word `sync`; `ez lock sync` no longer hints. sha256 is pinned at the same upstream rev but by its `package.bend` walk, `0xda83506fb9f059ead7afcfa2f498df5f`, which is the one upstream published on the hub; the smaller walk from `sha256.bend` ez pinned before was never on the hub, so ez could not be published. snap v1.0.0 answers stdout and stderr in the order they were written (SNAP-ANS-4), where the old pin gave stdout first; `tests/publishing.bend` now sets aside the stderr description line wherever it lands. eztoml stays at v0.1.0, as this RFC's rollout says: v0.4.0's round trip (TOML-RT-1 to TOML-RT-3) is still pending, and EZ-DOC-1 and EZ-LED-4 would rest on it.

Reading the code also turned up behavior that looked accidental and is not a requirement. Besides the ledger changes above, two such fixes were worth making, and both have landed. Every command, `ez help` included, created `.ez` and `bin` in the current directory, because `Env.make()` ran before the line was parsed; `Env.dirs` now names only the directories a command writes into, and nothing for most commands (`dirs_other`, `dirs_check`, `dirs_build`, `dirs_build_out`). And `ez doctor` failed a project with no dependencies, because it counted a lock that names no package as a problem even when the ledger needed none. The rest of what looked accidental was either covered by a decided change above or left alone as incidental, and what remains open is under "Known gaps".

### Known gaps

These are the things we know ez does not yet do, or does in a way we have not decided to guarantee. None of them is a requirement, and none weakens a proved row; each is here so that a reader does not have to rediscover it.

The Bend native runtime takes `--help`, `--threads` and `--gpu` anywhere on the command line before ez sees them, so `ez add --help` prints the runtime's usage and exits 0. `ez -h` is an unknown flag, since Shake binds no short help. Neither is ez's to fix from inside ez.

EZ-HASH-5 can still diverge from nix for bytes that are not UTF-8. The file effect reads a file as text, so a file whose bytes are not valid UTF-8 is serialized with its invalid bytes replaced and hashes differently from nix, the same bytes for every ez, so `ez lock` and `ez fetch` agree with each other and not with the nix build. A name that is not valid UTF-8 cannot be read back from the listing and stops the walk. Neither can be fixed from ez until Base can read a file's bytes.

The walk asks for a `LICENSE` by name, and bend lists the directory for one. On a disk that ignores case, a file named `License` is read as the `LICENSE` beside a published file by ez and not by bend, so the two hashes differ and `ez publish` refuses after the upload. `ez publish` also keeps bend's terms notice and license line to itself, so a package published with no `LICENSE` goes out as MIT-0 without ez saying so.

### How we will know it worked

The spec has done its job when the traceability check passes with no pending requirements in the EZ-DOC and EZ-RES groups, every remaining closed law has been deleted, and a rewrite of `ez lock` internals can be merged on the strength of the proof gate alone, without anyone re-deriving what an old example meant or running a test suite to feel safe.

The first two are met. bolt's `trace` rule runs at `error` against `SPEC.md`, every EZ-DOC and EZ-RES row is proved, and no closed law remains. The third is what the refactoring contract promises, and with every command in planner form it is now a matter of practice rather than of missing laws.

## Abandoned Ideas

### Witnessed and Conformance levels

An earlier draft of this RFC had four levels. Witnessed covered requirements checked on chosen examples through closed laws, and Conformance covered agreement with external oracles such as nix, checked against committed vectors by `ez test`. The appeal was coverage: nearly every requirement could be at some checked level on day one.

In practice both levels are tests under another name, and neither fits Bend. A Witnessed requirement is backed by closed laws, which carry every weakness described in Background while appearing on the same proof gate as real laws, so readers overestimate them. Conformance needs a runner that executes ez against oracle output, which puts a second gate beside the proof gate and makes `ez test`'s test lanes load-bearing. Both levels blur the one distinction the spec exists to draw. Collapsing them into Trusted costs nothing real, because an example-checked claim was never a guarantee, and it makes the remaining Proved requirements mean something.

### Keep converting tests into closed laws

The current direction, moving law-shaped `#|` tests into LAWS/PROOF, has real benefits. It moves checks to compile time, it makes the proof gate the one gate, and each conversion is small and mechanical, which suits agent-driven PRs.

The result is still a test suite checked at a different moment. Converting more of them increases the law count without increasing what is guaranteed, which is why the count has grown while confidence has not. The conversions were a useful inventory of what someone thought mattered, and the first rollout phase uses them exactly that way before retiring them.

### Keep ez test as part of the assurance story

Agents working on ez repeatedly argued that some behaviors, especially IO, could only be established by running tests. `ez test` was built to satisfy that, with caching, parallel lanes, and deadlines, and it does make an unchanged tree fast to re-check. It also became the program that runs the proof gate, which is the part CI relies on.

The argument for its test lanes holds only while IO behavior is unmodeled. Once commands have a planner form, IO decisions are ordinary pure functions and quantified laws cover them for every world, which is strictly more than any test run covers. What remains outside the planner is the interpreter, and a test of the interpreter against a real filesystem still only samples; it does not change the fact that interpreter faithfulness is trusted. So the specification depends on the proof gate, which moves into `ez prove`, and not on any test lane. The future of the test lanes is a separate decision.

### Prove properties directly over real IO

We could state laws over real IO commands with canned sessions against fake files, as bolt does, without a planner split. This avoids restructuring commands and reuses a technique that already works.

Canned sessions are closed: each fixes one fake filesystem and one transcript. They cannot quantify over worlds, so the frame and reproducibility properties that matter most (EZ-DOC-3, EZ-RES-6, EZ-VEN-3) stay out of reach. The planner split is what turns the fake world from a fixture into a variable.

### Formalize ez separately in Lean

Lean has tactics, a large library, and a mature kernel, so proving a model of ez there would be much less laborious than writing explicit Bend proof terms.

A Lean model would be a second implementation connected to the real code by nothing but good intentions. The value of Bend's approach is that laws are checked against the definitions that actually run. If Bend proof effort blocks a specific requirement, the right response under this spec is to mark it Trusted with a reason, not to prove a copy of it elsewhere.

### A byte-level lock round-trip

The first draft required that rendering a parsed lock reproduces the original bytes. ez never re-renders a parsed lock, and the TOML renderer it uses does no escaping, so that requirement would have forced us to prove a property of a code path nobody runs. Canonical order (EZ-DOC-2) plus parse-after-render (EZ-DOC-1) is what reproducibility actually needs, and we kept those.

## Rollout

The rollout proceeds in phases, each of which leaves the repo consistent. The decided behavior changes land as their own PRs alongside it; the only ordering between them is that a requirement cannot be proved before the change it depends on.

A preliminary phase makes ez lint clean under bolt v0.8.1: it fixes every style, correctness and suspicious finding (short parameter names, wrapping, doc comments, shadowing), none of which changes behavior, so that `mkLint` can join the flake checks with every group at `error` except the two law rules.

The first phase writes `SPEC.md` from this RFC, with the proved and pending status of each requirement, and sorts the existing closed laws using the law-by-law inventory: 43 that illustrate a Proved requirement are tagged with its ID, and 78 are deleted, along with the thirteen refactor-equivalence laws and their `old.*` definitions. It tags `pkg/hash_perm` with EZ-HASH-1. With the preliminary phase, it adds `mkLint` to ez's flake checks and moves `[tools.bolt]` to v0.8.1, with `closed` and `law` at `warn` and everything else at `error` in `bolt.bend`. This phase changes no behavior and immediately shows how far ez is from its own spec.

The second phase enables the traceability check in bolt, reading `SPEC.md`. Pending requirements do not fail it, so it can go on at once. `closed` is on at `error`, which keeps the closed laws from coming back; `coverage` (bolt v0.9.0's `law`) returns to `error` when the commands it grades are in planner form.

The third phase introduces the World model and converts `ez lock` to planner form, then proves EZ-DOC-1 through EZ-DOC-5, EZ-RES-4 through EZ-RES-6 and EZ-RES-8, EZ-VEN-1 through EZ-VEN-3, and EZ-HASH-2, deleting the closed laws each one subsumes. EZ-DOC-3 is proved once the lock input changes have landed. `ez lock` goes first because its guarantees are the most important. The design for this phase, with its World, its laws and its work packages, is in [ez-lock-planner.md](ez-lock-planner.md). The phase's upgrade laws (EZ-RES-4 to EZ-RES-6, EZ-RES-8 and the upgrade half of EZ-VEN-1) are stated over the ledger model the plan renders into ez.toml, so they held of the file's bytes only relative to EZ-LED-4, which was not in this phase. WP21 proved EZ-LED-4, and they now hold of the bytes.

EZ-DOC-1 is proved against the pinned eztoml v0.1.0 reader, with a file path holding `=` refused (see "Decided behavior changes"). Later, once eztoml states and proves its own render and parse round trip, ez moves to eztoml 0.2.x: EZ-DOC-1's text layer then rests on that pinned proof, as a Trusted row pointing at eztoml's requirement like the other pinned-dependency proofs, the `=` refusal lifts, and `bootstrap.sh`'s awk, which also cuts a pair at its first `=`, is fixed in the same change.

The next phase converts `ez add` and `ez remove`, with `ez init`, and makes the package walk a pure function of a checkout's files. It proves EZ-LED-2, EZ-LED-3, EZ-LED-7, EZ-RES-1 and EZ-RES-2, and lands the add and remove halves of EZ-LED-1, EZ-LED-6, EZ-LED-8, EZ-VEN-1, EZ-HASH-3 and EZ-OUT-2. Its design, with its Worlds, its laws and its work packages, is in [ez-add-planner.md](ez-add-planner.md). Later phases convert `ez fetch`, `ez publish`, `ez doctor` and the tool commands in the same way, one command per phase, each ending with its requirements proved.

ez stayed on bolt v0.9.0 while any `# toward` trail remained, because bolt retired `quantify` and its `# toward` exemption in favour of a strict `closed`, which the trails would fail. We deleted the last 40 trails in one change rather than one requirement at a time (see "Retiring closed laws"), and in the same change moved `[tools.bolt]` to the bolt that ships `trace` (a commit on bolt's main at first, since bolt v1.2.1), dropped `def quantify()` from `bolt.bend`, and set `closed` and `trace` to `error`. From then on the lint gate checks `SPEC.md` against the law tags mechanically.

The refactoring contract applies from the first phase, since it depends only on law statements and the trust boundary.

## How we got here

The rollout above ran as planned, with the command conversions split into work packages. The lock's are numbered WP0 to WP8 in [ez-lock-planner.md](ez-lock-planner.md), and those for `ez add`, `ez remove` and `ez init` are A0 to A7 in [ez-add-planner.md](ez-add-planner.md). The later commands took the next numbers, WP8 to WP13, and followed the add design's pattern, each recorded as an "Update" note there. Two packages share the number WP8: the lock design's NAR work and the conversion of `ez fetch`. Every package that changed behavior showed the change on the binary first, and "Decided behavior changes" records each one; the table below says only what each package proved.

| Step | What it did | Rows proved |
| :---- | :---- | :---- |
| Preliminary and first phase | Made ez lint clean under bolt, wrote `SPEC.md`, tagged `pkg/hash_perm`, deleted 78 closed laws and the thirteen refactor-equivalence laws, and kept 43 as `# toward` trails. | EZ-HASH-1 |
| Decided behavior changes | Landed the lock input changes, the tag, target and cache-key changes, `ez prove`, and the ledger fixes, each with quantified laws over its decision. | EZ-RES-3, EZ-TOOL-2 |
| Trails | Deleted the last 40 trails and moved to the bolt with a strict `closed` rule and `trace`, both at `error`. | |
| WP0, WP1 | String lemmas, then plain `ez lock` as a planner. | EZ-DOC-3, EZ-DOC-5 |
| WP2 | `ez lock --upgrade` in the same planner, as one plan. | |
| WP3, WP4 | Lock order, then lock read-back against eztoml v0.1.0. | EZ-DOC-2, EZ-DOC-1 |
| WP5a, WP5b | Idempotence of a plain lock, then of an upgrade. | EZ-DOC-4 |
| WP6 | The upgrade's moves. | EZ-RES-4, EZ-RES-5, EZ-RES-6, EZ-RES-8 |
| WP7 | Import rewriting and the allowlist's text layer. | EZ-VEN-2, EZ-VEN-3 |
| WP8 (lock design) | A pure NAR directory serializer. | EZ-HASH-2 |
| A0 to A7 | A pure package walk, then `ez remove`, `ez add` and `ez init` as planners. | EZ-LED-1, EZ-LED-2, EZ-LED-3, EZ-LED-6, EZ-LED-7, EZ-RES-1, EZ-RES-2 |
| WP8 (`ez fetch`) | `ez fetch` as a planner. | EZ-FETCH-1 |
| WP9 | The tool commands as planners. | EZ-TOOL-1, EZ-TOOL-3 to EZ-TOOL-9 |
| WP10 | The `ez lock` halves of three rows the add and fetch work had started. | EZ-LED-8, EZ-HASH-3, EZ-VEN-1 |
| WP11 | `ez publish` as a planner. | EZ-PUB-1, EZ-PUB-2, EZ-OUT-2 |
| WP12 | `ez doctor` as a planner. | EZ-VEN-4, EZ-VEN-5, EZ-LED-5 |
| WP13 | Exit statuses as pure functions of each command's end. | EZ-OUT-1 |
| WP15 | `ez run` as `cargo run`: the program on ez's own stdio and its status passed through, and a missing or unreadable ledger refused by `ez check`, `ez build` and `ez run`. | EZ-OUT-1, EZ-TOOL-9 |
| WP16 | `ez tool run` as `cargo run`: the built program on ez's own stdio, and the build's words on stderr. | EZ-TOOL-5, EZ-OUT-1 |
| WP17 | `ez add` prints the import line `ez publish` prints, for the entry's path inside the package. | EZ-RES-2 |
| WP18 | The import scan reads import lines as bend's loader does. | EZ-DOC-3 |
| WP19 | `ez doctor` checks the lock against the one `ez lock` would write, offline. | EZ-VEN-6 |
| WP20 | A NAR walk that reads the mode's exec bit and every name as listed, and `ez fetch` checking `narHash`. | EZ-HASH-7, EZ-FETCH-1 |
| WP21 | The ledger read back against eztoml v0.1.0, and `ez init`, `ez add`, `ez remove` and `ez lock --upgrade` refusing a ledger that would not. | EZ-LED-4 |
| WP23 | Named hub imports: the walk reads them as hub packages, the lock resolves and records each name under `[names]`, and `ez lock` and `ez fetch` lay the names files bend reads. | EZ-HUB-1 to EZ-HUB-4 |
| WP24 | `ez add <name>@<version>` records a named hub dependency: the hub's hash for the name, the package checked against it and laid with the name's file, and `[deps.<key>]` with `hub` and `hash`. | EZ-RES-2, EZ-RES-3, EZ-LED-7, EZ-HUB-1, EZ-HUB-4, EZ-OUT-2 |
| WP25 | `ez publish` publishes by name: `publish-as` and `version` in `[package]`, checked before anything is asked or sent, uploaded as `<publish-as>@<version>.0`, and the import line printed by that name. | EZ-PUB-2, EZ-PUB-3, EZ-OUT-2, EZ-LED-4 |
| WP26 | `ez init` lays out `main.bend`, opening with `# <name>: <description>`, and the `src/lib.bend` it imports, and `ez publish` prints the hub description just before it uploads. | EZ-INIT-1, EZ-INIT-2, EZ-PUB-4 |
| WP28 | `ez tool run`, `install` and `upgrade` on a plain Bend repository with no ez.toml, as `uvx` runs any package, and `--entry` to name the file built. | EZ-TOOL-4, EZ-TOOL-7, EZ-TOOL-9, EZ-OUT-2 |
| WP30 | `ez publish` asks the ledger's hub about every hub package the package imports, by hash and by name, and refuses, sending nothing, when one is not there or the hub cannot be asked. | EZ-PUB-5, EZ-OUT-2 |
| WP31 | shake v0.2.0 through its interface alone, snap v1.0.0, sha256 by its published walk, and ezhttp v0.5.0; the line laws restated over shake's `help_path`, `path_of` and `at`, resting on shake's proofs (EZ-TRUST-7). | EZ-OUT-1 |

Proving also found bugs that reading the code had missed, and each was fixed where it was found: WP6 found that WP2's upgrade read an empty refusal reason as no refusal (a case the interpreter never built, so the binary did not change), WP5b found that a tool pin with a rev and no narHash moved on the next upgrade, WP7 found the allowlist written twice for a shared tree, and WP10 found a lock that accepted a manifest `ez fetch` would then refuse. The proofs are long, as the risks below expected: `lock/PROOF.bend` grew by about 4,800 lines in WP5b alone, most of them one lemma per step of the upgrade.

## Risks

### Proof effort in Bend

Bend has no tactics or proof search, so quantified laws over strings, TOML documents, and maps require long explicit proofs, and some requirements may cost more to prove than they are worth. `pkg/PROOF.bend` is 2350 lines for 40 laws, most of it the permutation argument behind EZ-HASH-1. With only two levels, the escape hatch is explicit: a requirement that proves too expensive moves to Trusted with a written reason. That is a visible, reviewable weakening rather than a silent one, and we order the work so that structural properties (order independence, framing, idempotence) come before content properties.

### The model can diverge from reality

A law about the World model is only as good as the model. If the model says git reports ancestry one way and real git behaves differently, the proof holds and the tool is still wrong. We accept this, keep the model's fields to what the code actually reads, and list every such assumption in the trust boundary so it is at least visible.

### The spec encodes accidents

Writing requirements from current behavior risks promoting bugs into guarantees. This revision checked every requirement against the code, and a maintainer decided each disagreement between the code and the README, either correcting the requirement or deciding a behavior change. Behavior we found to be accidental is kept out of the requirements, and what is still open is listed under "Known gaps" rather than promoted.

### Headline guarantee requires a behavior change

EZ-DOC-3 did not hold when we wrote it, and no refactor could make it hold, because `ez lock` read inputs a clone does not have. The inputs it may read were decided, and the changes that enforce them are behavior changes with their own risk: fetching non-vendored dependencies makes plain `ez lock` need the network where it silently did without before, and dropping `[lock] bend` changed every existing lock file once. Until those landed, EZ-DOC-3 stayed pending, and the spec said so plainly rather than implying reproducibility the tool did not have. They have landed, and WP1 proved the row.

### Pressure to reintroduce tests

Agents that previously argued for tests will likely argue again, especially for interpreter code. The refactoring contract is the answer: interpreter faithfulness is Trusted, a test does not change that, and a PR that adds tests as a condition of merging is adding a gate the spec does not recognize.

### Checker soundness

Every Proved requirement assumes the Bend checker is sound (EZ-TRUST-1). We cannot fix this from ez. The flake already pins Bend versions and bumps them in their own PRs, which gives us a natural place to re-check the laws against each new checker.

## Future Steps

The same structure applies directly to the sibling libraries. ezjson, eztoml, and ezhttp already describe their laws in terms of external standards (TOML 1.0, RFC 9110, RFC 3986), and a shared traceability rule in bolt would cover all of them with the same two levels. ezhttp now owns the HTTP laws, and ez's EZ-TRUST-5 row points at them. Re-checking a dependency's PROOF.bend at its pinned hash inside ez's gate would turn such a row back into a proof without a third level.

ez stays on eztoml v0.1.0 until eztoml states a quantified render and parse round trip. Its 0.2.x line has only closed laws, so moving to it now would trade EZ-DOC-1's and EZ-LED-4's proved text layer for an unproved one. When it states one, both rows rest on it, and the lock's refusal of a path holding `=` and `bootstrap.sh`'s awk, which cuts a pair at its first `=`, go in the same change.

Once `ez lock` and `ez add` are both in planner form, the World model makes cross-command guarantees expressible, such as "`ez add` followed by `ez lock` on a fresh clone reproduces the lock `ez add` wrote." Those end-to-end statements are the strongest description of what ez is for, and they become provable only once individual commands are pure.

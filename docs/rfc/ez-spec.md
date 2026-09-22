# RFC: A Behavioral Specification for ez

## Draft Status

State: Draft

The first draft was written from the README, the PR history, and the Bend LAWS/PROOF conventions, without the source. This revision replaces those assumptions with what the code at `b28ca2c` does. The evidence for every change is in [ez-law-inventory.md](ez-law-inventory.md), which lists every existing law and the findings from reading each command.

Items for review:

- [x] <!-- REVIEW (resolved): Function names in the law sketches were placeholders. They now name real definitions, or say that none exists yet; see "Names used in this document". -->
- [x] <!-- REVIEW (resolved): The requirement list was derived from the README. Each requirement has been checked against the code; the verdicts are in the inventory, and requirements were corrected, added or removed to match. The items below are the ones where code and intent may differ and a person has to decide. -->
- [x] <!-- REVIEW (resolved): Whether bolt is the right home for the traceability check. bolt already has a `laws` rule group with `closed`, `law` and `unsafe` rules, which is where the check belongs. What remains open is the format question below. -->
- [ ] <!-- REVIEW: EZ-DOC-3 remains the headline guarantee, and it does not hold today. On a fresh clone of this repository, `ez lock` writes empty `files` tables for the three non-vendored git dependencies and exits 0. It also reads the installed bend version, `BEND_HUB`, the hub over the network, `.ez/origins.toml`, and untracked `.bend` files. We need a decision on which of these belong in `inputs`, the draft's `agree_on_inputs` (see "What ez lock may read") before its law can be stated. -->
- [ ] <!-- REVIEW: `Sha.hex` hashes each character's low byte, not the file's UTF-8 bytes, so for non-ASCII text it is not SHA-256 of the file. `nix/bend-lib.nix` says this is Bend's own fold. Confirm that it is intended, since EZ-HASH-4 depends on it matching Bend, and that `sha/nar.bend` encoding to UTF-8 while `sha/sha.bend` does not is also intended. -->
- [ ] <!-- REVIEW: The gitignore allowlist (EZ-VEN-1) is written only by `ez lock --upgrade`. `ez add` never writes it, `ez remove` never removes it, and `ez init` writes `.ez/`, which makes every allowlist line inert. Decide which commands own the allowlist before this requirement can be stated. -->
- [ ] <!-- REVIEW: There is no `ez: <area>:` error convention in the code. We replaced EZ-OUT-1 with the exit-status rule the code does follow. Decide whether a message prefix should become a requirement; adopting one is a behavior change. -->
- [ ] <!-- REVIEW: `ez add` tag selection lets a pre-release win (`v2.0.0-rc1` over `v1.9.0`), never asks the remote for its default branch, and resolves the chosen name with a tail-matching `ls-remote`, so `main` can resolve to `refs/heads/feature/main`. EZ-RES-1 is stated as the code behaves; confirm each of these is intended. -->
- [ ] <!-- REVIEW: Target classification treats `owner/repo` as GitHub only when both segments are letters, digits, `-` and `_`, so `vercel/next.js` is a local path. EZ-RES-3 is stated as the code behaves; confirm. -->
- [ ] <!-- REVIEW: The tool cache key (`<dir>/rev`) does not record which file was built or with which bend, so a pinned tool with an `entry` override and a free run of the same repo at the same rev can share a binary. EZ-TOOL-2 is stated with that limit; decide whether the key should change. -->
- [ ] <!-- REVIEW: `ez publish` compares its hash with bend's after `bend --publish` has uploaded. EZ-PUB-2 is stated over the decision, not the ordering; decide whether publish should refuse before uploading. -->
- [ ] <!-- REVIEW: The proof gate is run today by the proof lane of `ez test`, invoked by `mkProofs` in `flake.nix`. The spec depends on the gate and not on `ez test`'s test lanes. Decide whether the proof lane stays inside `ez test` or moves to its own command or to `mkProofs` directly. -->
- [ ] <!-- REVIEW: The traceability check needs a requirement list bolt can read. bolt reads only `.bend` sources today. Decide whether the requirement IDs live in a Bend file (for example a `SPEC.bend` of defs) or bolt learns to read `SPEC.md`. -->
- [ ] <!-- REVIEW: bolt's `closed` rule already flags every law with no binder, and ez's `bolt.bend` sets the `laws` group to `error`. Adding `mkLint` to the flake checks would fail on all 122 closed laws. Decide whether `closed` runs at `warn` until the first rollout phase has sorted them, or whether `mkLint` waits. -->
- [ ] <!-- REVIEW: Thirteen laws hold a rewritten definition equal to the one it replaced (`join_agrees`, `dechunk_agrees` and so on), and many quantified laws are lemmas with no requirement. The draft allows untagged quantified laws and does not protect them. Decide whether refactor-equivalence laws are deleted once their rewrite has landed. -->
- [ ] <!-- REVIEW: Guarantees proved in a pinned dependency (SHA-256 in bend-sha256, HTTP framing in ezhttp once `net/` moves there) are Trusted from ez's side, because ez's gate does not re-check them. Confirm that, rather than having ez's gate check the dependency's PROOF.bend at the pinned hash. -->
- [ ] <!-- REVIEW: The draft deletes closed laws once their requirement has a quantified law, and deletes untagged closed laws outright. Confirm you want them gone rather than kept as non-normative examples. -->
- [ ] <!-- REVIEW: The inventory lists behavior that looks accidental (every command creates `.ez` and `bin` in the current directory, `ez init` overwrites an existing ledger, `ez add` names a dependency after its entry file so two `main.bend` entries collide, and others). None of it is a requirement. Confirm none of it should be. -->

---

## Abstract

ez has 269 laws across ten LAWS.bend files. 122 of them are closed equalities, most moved over from `#|` tests, so they pin exact outputs for specific inputs rather than stating what ez guarantees. This RFC defines a behavioral specification for ez in which every requirement is either **Proved** by a quantified law or explicitly **Trusted** as an assumption about the environment, with nothing in between. It adds a model of the state each command reads and writes, so that IO behavior can be stated as laws, and a refactoring contract that says exactly which statements a change must preserve.

## Glossary

| Term | Meaning |
| :---- | :---- |
| Ledger | `ez.toml`. The human-edited record of the package, its `[deps.*]`, and its `[tools.*]`. |
| Lock | `ez.lock.toml`. The machine-written record of the hub, the bend version, every package with its source and files, and every tool pin. |
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

### How ez proves things today

Bend's verification model splits claims from proofs. LAWS.bend holds the statements, PROOF.bend holds a definition that proves each one, and `bend PROOF.bend` fails until every law is discharged. Proofs are terms built from pattern matching, recursion as induction, and equality rewrites. There are no tactics and no proof search.

A passing exit status is not enough. `bend` exits 0 and prints `All terms check, but N defs rely on unsafe or foreign code:` when a proof leans on an unchecked def, and a def that never returns proves anything. The gate ez actually runs reads the first line of output and accepts only the bare `All terms check.` (`ez/test.bend:545-558`). That stricter reading is what we mean by the proof gate throughout.

Today the gate runs inside `ez test`. `ez test` finds every PROOF.bend, runs `bend` on each alongside its test lanes, and reports a proof as passed only on that exact line. `flake.nix` runs `ez test --js-only --unit-only` through `mkProofs`, and that is the only place CI checks the laws. `ez test` caches a passed proof in `.ez/cache`, keyed on the bend version, `$CC`, and the hash of the proof's import closure; `mkProofs` builds from a clean copy of the source, so in CI the cache is always empty.

ez adopted this model through a series of PRs that moved "law-shaped" equalities out of `#|` test trailers and into LAWS/PROOF across the sha, pkg, lock, git, net, pub, manifest and ez areas. The result is uneven. The inventory counts 147 quantified laws and 122 closed ones. The quantified laws include one real guarantee (the 0x hash does not depend on the order files were found in), a strong model of the ledger, the HTTP client's framing, the decision functions of `ez publish`, a path algebra, and thirteen laws that hold a faster rewrite equal to the definition it replaced. Every law about upgrade decisions, lock rendering, import rewriting, the gitignore allowlist, target classification, NAR hashing and SHA-256 is closed. Of the 94 laws in `ez/LAWS.bend`, 42 are about the `ez test` runner itself and 19 pin progress or error wording.

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

We are not proving Bend itself, git, the hub, nix, or the host filesystem correct; those are trust assumptions and the spec names them. We are not specifying `ez test`'s test lanes, and nothing in this specification depends on running a test. We are not changing ez's user-facing behavior in this RFC; where the spec and the current behavior disagree, we record the disagreement and decide separately.

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

A guarantee proved in a dependency is Trusted from ez's side. The SHA-256 digest comes from Giulio2002/bend-sha256, whose own laws hold it to an executable FIPS 180-4 specification, and HTTP framing will be proved in ezhttp once `net/` moves there. Those proofs are real, but ez's gate does not re-check them, so ez records them as trust with the dependency and pinned hash as the reason.

A Proved requirement whose law has not landed yet is marked **pending** in `SPEC.md`. Pending is a status, not a third level: it means "intended to be Proved, not yet guaranteed", and the spec says so plainly. Because the gate fails on any undischarged law, a pending requirement's law stays out of LAWS.bend until its proof is written, and the statement lives in `SPEC.md` until then.

### The proof gate

The specification depends on one mechanical check: for every PROOF.bend in the tree, `bend PROOF.bend` prints exactly `All terms check.` as its first line. It does not depend on which program runs that check. Today it is the proof lane of `ez test`, run by `mkProofs` in `flake.nix`; the test lanes that run beside it are outside the specification. The runner's faithfulness is a trust assumption (EZ-TRUST-4), in the same way the interpreter's is.

### The World model

Laws can only quantify over values, and most of ez's behavior is IO. We close that gap by modeling what a command can see as a value and splitting each command into a pure planner and a thin interpreter.

The fields below are what `ez lock` actually observes today, taken from tracing the command (see "What ez lock reads" in the inventory). None of these types exists in the code yet.

```
# New types. Field names are proposals; every field is something the
# current code reads.
type World:
  ledger: String                      # ez.toml text
  tree: Map(Path, String)             # the files a walk from the project root sees
  lib: Map(Hash, Pkg)                 # manifests and files under $BEND_LIB
  origins: String                     # .ez/origins.toml text
  env: Map(String, String)            # BEND_LIB, BEND_HUB, HOME, XDG_*, EZ_TOOL_BIN
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

A World that holds whole remotes is a lazy value in spirit: the interpreter only needs to read the parts a planner asks for. For `ez lock` without `--upgrade` the planner reads `ledger`, `tree`, `lib`, `origins`, `env`, `bend` and `hub`, and reads `remotes` only when a tool pin lacks a `rev` or `narHash`. With `--upgrade` it also reads `remotes` and `.gitignore` through `tree`.

We do not need to convert every command before the spec is useful. The spec is written against the model from the start, and each command moves to planner form when its requirements move from pending to proved.

### How far ez lock is from planner form

Much of the pure half already exists. `origin` and `origins.all` choose where a package comes from (`lock/lock.bend:137-195`). `U.aim`, `U.judge`, `U.retarget`, `U.reallow.many` and `U.reimport.many` decide upgrades and compute the rewritten ledger, gitignore and sources (`manifest/upgrade.bend`). `Lock.render.tools` turns packages and tools into the lock's text. `K.hash_of` and `K.manifest_of` are pure.

What is not pure is the control flow between them, spread across roughly forty IO functions. Three places matter most. The package set grows from IO results: `resolve` reads or fetches a package, scans its text for imports, and queues what it finds, dying on the first bad package in walk order. A decision is made inside IO: `read.git` turns a missing manifest into an empty file list (`lock/lock.bend:287-293`), which is the bug that breaks EZ-DOC-3. And `--upgrade` runs three phases (`Up.run`, `Pin.upgrade`, `lock.now`) that communicate by writing ez.toml and `.ez/lib` and reading them back, so the final lock depends on the order of writes, and a failure in a later phase leaves earlier writes in place.

Converting `ez lock` means turning `roots` and `resolve` into a pure fold over `World.tree`, `World.lib` and `World.hub`, making the three upgrade phases one planner that threads the ledger through as a value, and moving the "missing tree" case out of `read.git` into an explicit outcome.

### Names used in this document

The law sketches below use these names. Where no definition exists, the sketch introduces one.

| Name in a sketch | Real definition |
| :---- | :---- |
| `K.hash_of` | `pkg/pkg.bend:530`. The 0x name of a file list. |
| `K.pkg_of` | `pkg/pkg.bend:556`. Walks an entry's import closure and returns the package (IO). |
| `perm` | `pkg/LAWS.bend`. Lehmer-coded rearrangement of a file list; law vocabulary only. |
| `Nar.path` | `sha/nar.bend:447`. The narHash of a directory (IO). No pure `Nar.of_tree` exists yet. |
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

The requirements below are the first version of `SPEC.md`. Each one is stated as behavior, not implementation, and was checked against the code. The Status column is `proved` when a tagged quantified law already exists and `pending` otherwise. Where the code does not yet behave as a requirement says, the inventory records the finding and the requirement carries a REVIEW marker in Draft Status.

#### Hashing (EZ-HASH)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-HASH-1 | The 0x hash of a file list with distinct paths depends only on its (path, sum) pairs, not on the order they were found in. | Proved | proved |
| EZ-HASH-2 | The NAR serialization of a directory does not depend on the order its entries are listed in. | Proved | pending |
| EZ-HASH-3 | When ez writes a package under `<lib>/<h>`, `h` is the 0x hash of the file list whose manifest it writes beside the files. | Proved | pending |
| EZ-HASH-4 | ez's 0x hash for an entry equals the hash `bend --publish` assigns to it. | Trusted | |
| EZ-HASH-5 | ez's narHash equals `nix hash path --type sha256 --sri` of the same tree. | Trusted | |
| EZ-HASH-6 | `Sha.hex(s)` is the SHA-256 of the bytes formed by each character of `s` reduced to its low eight bits. For ASCII text that is SHA-256 of the file's bytes. | Trusted | |

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

EZ-HASH-2 is true by construction: `sha/nar.bend` lists a directory with `find` and sorts the names with an insertion sort on `String.is_le` before serializing. It is not stated because the serializer reads the filesystem as it goes. Stating it needs a pure `Nar.of_tree(t: Tree) -> String` that `Nar.path` calls after reading, and then a law like the one above over permutations of each directory's entries.

EZ-HASH-3 holds when a tree is written, because `Git.lay` names the directory and writes the manifest from the same file list. Nothing re-checks it afterwards, which is why it is stated about the write and not about the directory at rest.

The split in this group shows how the two levels work together. We cannot prove that ez agrees with nix or with Bend's publisher, because those are other programs, so EZ-HASH-4 and EZ-HASH-5 are Trusted. The inventory lists the ways EZ-HASH-5 can diverge today (exec bit from `test -x`, trimmed names and symlink targets, names with newlines, submodules). EZ-HASH-6 is restated from "computes FIPS 180-4 SHA-256" to what `Sha.hex` does, since for non-ASCII input it is not SHA-256 of the file.

The closed laws for the FIPS `abc` vector, the empty string and the empty NAR directory back these requirements only as examples. They are removed in the first rollout phase.

#### Ledger (EZ-LED)

These requirements are new in this revision. The ledger code already has the strongest quantified laws in ez, and the draft did not list them.

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-LED-1 | A ledger that does not parse is never read into a model, and renders as nothing, so no command writes a guess over it. | Proved | pending |
| EZ-LED-2 | Adding a dependency to a ledger model twice is adding it once. | Proved | pending |
| EZ-LED-3 | Removing a dependency from a ledger model twice is removing it once. | Proved | pending |
| EZ-LED-4 | A ledger ez rendered parses back to the model it was rendered from. | Proved | pending |
| EZ-LED-5 | A `[tools.*]` section is a tool, never a dependency, and needs no `hash`. | Proved | pending |

EZ-LED-1 to EZ-LED-3 have quantified laws today (`read_refuses_a_problem`, `render_of_unread_is_blank`, `add_idem`, `remove_idem`), and are pending only because the laws are untagged and state the model edit, not the command. `ez add` does not call `R.add` on the parsed ledger as it stands: it forces `vendor = false` and re-renders the whole file, so re-adding a dependency drops `vendor = true`. The requirement is over the model edit; the command's use of it is part of converting `ez add` to planner form. EZ-LED-4 has one closed example (`render_parse_roundtrip`).

#### Lock document (EZ-DOC)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-DOC-1 | Parsing a rendered lock yields the packages, hub and tools that were rendered. | Proved | pending |
| EZ-DOC-2 | Packages are written in hash order and each package's files in path order, so the lock's text does not depend on the order the walk found them in. | Proved | pending |
| EZ-DOC-3 | `ez lock` output is a function of the ledger and the committed tree. A fresh clone reproduces the lock byte for byte. | Proved | pending |
| EZ-DOC-4 | `ez lock` is idempotent: run on the world it just produced, it writes the same bytes. | Proved | pending |
| EZ-DOC-5 | `ez lock` without `--upgrade` never changes a dependency's pinned rev, and changes a tool's only when the ledger left it empty. | Proved | pending |

EZ-DOC-2 replaces the draft's "rendering a parsed lock reproduces the original bytes". No code path re-renders a parsed lock, and the TOML renderer does no escaping, so that statement was about a function ez does not have. What the lock does guarantee is canonical order: `pack.sort` and `K.files_of` sort before rendering, and `pack_ins_le` already states one step of it.

EZ-DOC-3 is the headline guarantee of the whole tool, and it does not hold today. The README says `root` and `narHash` exist so that `ez lock` never has to consult anything a clone does not have, and that part is true: plain lock copies them from the ledger and never recomputes them. But plain lock also reads the untracked trees under `$BEND_LIB`, and when a non-vendored git dependency's tree is missing it writes an empty `files` table and exits 0. On a fresh clone of this repository that happens to shake, eztoml and snap. As a law, EZ-DOC-3 is a frame property, and stating it forces us to define exactly what the lock may read:

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

Tracing the command gives the set `ez lock` reads today. We sort it into what EZ-DOC-3 already allows, what it cannot allow, and what needs a decision.

The ledger and the committed files a walk from the project root reaches belong in `inputs` by definition. So do the vendored trees under `.ez/lib`, since they are committed.

Two inputs cannot be in `inputs` if EZ-DOC-3 is to mean anything. The first is the untracked trees under `$BEND_LIB` for non-vendored git dependencies, which a clone does not have; the lock must get their file lists some other way (for example by fetching at the ledger's rev and checking `narHash`) or refuse. The second is `.ez/origins.toml`: `origin_agrees` already proves it cannot override the ledger for any hash the ledger names, but a hash only the cache names still locks differently on a clone. Untracked `.bend` files found by `find` fall in the same group.

Three inputs need a decision. The `[lock] bend` field records the installed bend version, so two machines with different bends write different locks. The `[lock] hub` field and the hub itself come from `BEND_HUB` and the network; hub content is addressed by hash and verified on arrival, so it may be reasonable to include "the hub serves what was published" as a trust assumption rather than an input. And `Pin.fill` reaches git and the network when a tool pin lacks a `rev` or `narHash`, and writes ez.toml during a plain lock.

The inventory's table lists every input with its source line.

#### Resolution (EZ-RES)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-RES-1 | `ez add` with no ref pins the greatest semver-ish tag on the remote; with none, `main`; with no `main`, `master`; with neither, it refuses with exit 1. A 40-hex ref is used as a commit without asking the remote. | Proved | pending |
| EZ-RES-2 | `ez add` with no entry uses the revision's `[package] entry`, then `[package] bin`, then `main.bend`, and refuses if that file is not in the revision. | Proved | pending |
| EZ-RES-3 | A target containing `://` or starting `git@` is a git URL. A target starting `/`, `./`, `../` or `~/` is a path. A target of exactly two segments of letters, digits, `-` and `_` is `https://github.com/<target>`. Anything else is a path. | Proved | pending |
| EZ-RES-4 | `ez lock --upgrade` never moves a hub dependency. | Proved | pending |
| EZ-RES-5 | An upgraded rev-only dependency moves to the default branch tip only when its pin is an ancestor of that tip, and stays a commit pin. Otherwise the upgrade refuses with exit 1. | Proved | pending |
| EZ-RES-6 | `--package NAME` asks the remote only for the named dependency or tool, and every other ledger entry keeps its rev, tag and hash. | Proved | pending |
| EZ-RES-7 | Tags, refs, and ancestry reported by git are accurate. | Trusted | |
| EZ-RES-8 | An upgraded tagged dependency re-resolves its tag. A tag that now names a commit the pin does not descend to, or a pinned commit whose tree no longer hashes to the pin, stops the upgrade with exit 1. | Proved | pending |

"Semver-ish" in EZ-RES-1 is what `git/git.bend` accepts: an optional `v` or `V`, one or more dot-separated numeric parts, an optional pre-release after `-`, and anything after `+` ignored. The comparator pads missing parts with zero and ranks a release above its own pre-release. EZ-RES-1 and EZ-RES-2 are precedence rules, and each becomes a law over every list of tags or every manifest. Today they have no law at all, and `Git.latest` and `Git.default.ref` mix the choice with the `ls-remote` calls.

EZ-RES-6 is narrowed from the draft's "every other lock entry is unchanged". The final step of an upgrade recomputes the whole lock from the current world, so other entries are unchanged only when nothing else changed, which is EZ-DOC-3's job. What `--package` itself guarantees is about the ledger:

```
# EZ-RES-6
law upgrade_one_frames_others:
  for w: World
  for n: String
  for m: String
  for e: {String.eq(n, m) == False{} : Bool}
  {M.dep(upgrade_plan.ledger(w, n), m) == M.dep(M.parse(w.ledger), m) : M.Dep}
```

EZ-RES-8 is new. The code refuses on a moved tag and on drift, and closed laws (`tag_moved_off`, `same_rev_drifts`) show the verdicts. In the dependency path the drift decision is made after the new tree has been laid, by `confirmed` in `ez/upgrade.bend`, and `U.judge` is called with its agreement bit fixed to true, so its `Drift` arm cannot fire there.

EZ-RES-5 and EZ-RES-8 are proved relative to EZ-RES-7. The law says ez moves a pin only when the model's ancestry relation says so; whether that relation matches the real repository is git's responsibility.

#### Vendoring and source rewriting (EZ-VEN)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-VEN-1 | When `ez lock --upgrade` moves a vendored dependency's hash, the `.gitignore` line `!.ez/lib/<old>` becomes `!.ez/lib/<new>`, and a missing line is appended. | Proved | pending |
| EZ-VEN-2 | When an upgrade moves a hash, every line of a `.bend` file outside `.ez` and `.git` that starts `import <old>/` names `<new>` afterwards. | Proved | pending |
| EZ-VEN-3 | Import rewriting leaves every other line of every file byte-identical, and does not write a file with no matching line. | Proved | pending |
| EZ-VEN-4 | `ez doctor` never writes to the project's source files. | Proved | pending |

EZ-VEN-1 is narrowed from the draft's "the allowlist names exactly the hashes of dependencies marked `vendor = true`", which is not true: `ez add` never writes the allowlist, `ez remove` never removes a line, and `ez init` writes `.ez/`, under which git ignores every allowlist line. The narrowed statement is what `U.reallow.many` does.

EZ-VEN-2 and EZ-VEN-3 together specify rewriting completely: the first says what changes, the second says nothing else does. The match is exact at column 0, so an indented import (which the package walk accepts) is not rewritten; the requirement states the column-0 rule so that a change to it is a behavior change. Swaps apply one after another, so the law should quantify over swap lists with distinct old and new hashes. The single closed example, `imports_follow_hash`, covers both requirements on one file.

EZ-VEN-4 holds today (`ez/doctor.bend` has no file write) and is only provable because of the planner split, where it becomes a claim that the plan `doctor_plan` returns contains no effect under the project root other than the directories every command creates. Every command runs `Env.make()` first, which creates `.ez`, `bin` and the library directory; that is recorded as accidental in the inventory.

#### Fetch (EZ-FETCH)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-FETCH-1 | `ez fetch` writes a package file under `BEND_LIB` only when its digest matches the lock: a hub body's digest starts with the lock's sum, a git file's digest equals it. | Proved | pending |

This replaces the draft's EZ-TRUST-3 ("the hub serves the tree whose hash was requested"). ez does not trust the hub: `Hub.judge` refuses a body that does not hash to what was asked for, and the three quantified `hub/judge_*` laws state the verdicts. What remains trusted is SHA-256 itself. `ez fetch` does not check `narHash`, and it trusts a cached tree whose manifest text matches without re-reading its files; both are recorded in the inventory.

#### Tools (EZ-TOOL)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-TOOL-1 | The link directory is `$EZ_TOOL_BIN`, else `$XDG_BIN_HOME`, else `$HOME/.local/bin`, an empty value counting as unset. | Proved | pending |
| EZ-TOOL-2 | A cached checkout and binary are reused only when the recorded commit equals the resolved commit, and never when the resolved commit is empty. | Proved | pending |
| EZ-TOOL-3 | A local target with uncommitted or untracked changes, or a path that is not a checkout, resolves to no commit and is rebuilt on every run. | Proved | pending |
| EZ-TOOL-4 | A target naming a `[tools.*]` pin in ez.toml builds the lock's rev, url, entry and bin. An `owner/repo` or URL target builds `git ls-remote <url> HEAD`. A path builds its clean `HEAD`. | Proved | pending |
| EZ-TOOL-5 | `ez tool run` exits with the built program's status; any failure before the program runs exits 1. | Proved | pending |
| EZ-TOOL-6 | `ez tool install` and `ez tool upgrade` never run the built binary. | Proved | pending |
| EZ-TOOL-7 | The built file is the pin's `bin`, then the pin's `entry`, then the checkout's `bin`, then its `entry`, then `main.bend`. The link is named after the checkout's package name, or `app`. | Proved | pending |
| EZ-TOOL-8 | A remote target whose cache slug is empty, absolute, or climbs with `..` is refused. | Proved | pending |

EZ-TOOL-2 is weaker than the draft's "both correspond to the resolved commit". One file records the commit for both the checkout and the binary, and it does not record which file was built or with which bend, so the requirement states only what the key covers. EZ-TOOL-7 and EZ-TOOL-8 are new; closed laws for them exist in `ez/LAWS.bend` (`file_*`, `out_name*`, `target_escapes`).

EZ-TOOL-5 is stated over the planner's outcome, not over a real process. The planner returns a run effect as its final effect after a successful build and exit 1 on every earlier failure; the interpreter passing the child's status through unchanged is covered by the interpreter trust assumption. The program runs with stdin at `/dev/null` and its output buffered until it exits; that is interpreter behavior and not part of the requirement.

#### Publish (EZ-PUB)

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-PUB-1 | `ez publish` refuses when `git status --porcelain --untracked-files=normal` names any path. | Proved | pending |
| EZ-PUB-2 | `ez publish` succeeds only when a line of bend's output is exactly a `0x` name and equals ez's own hash. Any other answer exits 1. | Proved | pending |

Both are new. `pub/LAWS.bend` already proves the decision functions for all inputs (`clean_is_all_blank`, `answer_is_a_name`, `unread_never_agrees`, `differs_never_agrees`); what is pending is stating them over the command's plan. EZ-PUB-2 describes the verdict, not the ordering: today the comparison runs after bend has uploaded.

### Outcomes and incidental output

Much of the brittleness in today's closed laws comes from pinning whole outputs. The spec separates output into two kinds.

**Contractual output** is anything a user or a script can reasonably depend on: exit statuses, the bytes of files ez writes (lock, ledger, gitignore, rewritten imports), link paths, and effect plans. Requirements talk only about contractual output.

**Incidental output** is everything else, mainly human-readable progress and error wording. There is no consistent error format in ez today: failures are reported as `ez: <prose>`, `ez: <path>: ...`, `ez: git <subcmd>: ...`, `ez: error: ...`, Shake's unprefixed `error: ...`, or a subprocess's own output with no ez line at all. Planners should return a structured outcome and a separate renderer should turn it into text, so that laws are stated over the outcome and a change that rewords a message touches the renderer and no law. The one output rule the code does follow consistently is the exit status:

| ID | Requirement | Level | Status |
| :---- | :---- | :---- | :---- |
| EZ-OUT-1 | Every command exits 0 on success and 1 on any failure ez detects, except `ez tool run`, which exits with the program's status. | Proved | pending |

This replaces the draft's `ez: <area>:` prefix requirement, which the code does not implement. The 19 closed laws that pin progress and error wording (`hub_404_teaches`, `drift_names_the_tag`, `installed_names_the_link` and the rest) point toward no requirement and are deleted in the first rollout phase.

### Retiring closed laws

Closed laws have no standing in this specification. They are not a level, they cannot carry a requirement tag, and nothing in the refactoring contract protects them. We retire them in two steps.

In the first rollout phase, every existing closed law is sorted against the requirement list, using the inventory's "Points toward" column. A closed law that illustrates a requirement is kept temporarily and marked with the ID it points toward, so the pending requirement has a visible trail. A closed law that fits no requirement is deleted, since it pins behavior nobody has decided to guarantee. By the inventory, that deletes the closed laws about the `ez test` runner, the CLI parser, progress wording and the spinner's terminal choice.

When a requirement's quantified law lands, the closed laws pointing at it are deleted in the same PR. The quantified law strictly subsumes them, and keeping them would reintroduce exactly the brittleness this RFC removes.

bolt already enforces the end state. Its `closed` rule flags every law in a LAWS.bend with no `for` or `exs` binder.

### Tagging and traceability

Every quantified law that proves a requirement carries a comment naming it:

```
# EZ-RES-6
law upgrade_one_frames_others: ...
```

A check reads the requirement list and every LAWS.bend and fails when:

- A requirement at level Proved, marked proved, has no quantified law tagged with its ID.
- A law is tagged with an ID that does not exist in the requirement list.
- A tagged law has no binders.
- A requirement at level Trusted has no row in the trust boundary table.

It reports, without failing, every requirement still pending. That report is the honest answer to "what does ez prove right now", and it shrinks as proofs land.

Untagged quantified laws are allowed. ez has many of them: path lemmas, string lemmas, the ledger reading laws that support EZ-LED, and thirteen refactor-equivalence laws that hold a rewrite equal to the definition it replaced. They pass the gate like any law, but the refactoring contract does not protect them, so a change may edit or delete them freely.

The check belongs in bolt, as a rule in the `laws` group next to `closed`, `law` and `unsafe`, run through `mkLint`. It depends only on file contents, which keeps it inside the lint gate rather than adding a new runner. Two things have to change on ez's side for it to run: ez's flake checks do not include `mkLint` today, and bolt reads only `.bend` sources, so the requirement list either lives in a Bend file or bolt learns to read `SPEC.md`.

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
| EZ-TRUST-4 | The gate runner runs `bend` on every PROOF.bend in the tree and passes only on an exact `All terms check.` first line. | It is ez code (the proof lane of `ez test`) run by `mkProofs`, not a law. In CI its cache is empty, so every proof is re-checked. |
| EZ-TRUST-5 | HTTP framing and URL parsing are correct. | Proved in ezhttp at the hash ez pins, once `net/` moves there; ez's gate does not re-check it. |
| EZ-RES-7 | git reports refs, tags, and ancestry accurately. | The World model takes git's answers as given. |
| EZ-HASH-4 | ez's 0x hash matches `bend --publish`. | The publisher is a separate program. |
| EZ-HASH-5 | ez's narHash matches nix. | nix is a separate program. |
| EZ-HASH-6 | `Sha.hex` computes the SHA-256 digest of its folded bytes. | Proved in Giulio2002/bend-sha256 against an executable FIPS 180-4 specification, at the hash ez vendors; ez's gate does not re-check it. Collision resistance is also assumed. |

EZ-TRUST-3 from the first draft is removed: ez verifies hub content itself (EZ-FETCH-1), so what remained of it was EZ-HASH-6.

### How we will know it worked

The spec has done its job when the traceability check passes with no pending requirements in the EZ-DOC and EZ-RES groups, every remaining closed law has been deleted, and a rewrite of `ez lock` internals can be merged on the strength of the proof gate alone, without anyone re-deriving what an old example meant or running a test suite to feel safe.

## Abandoned Ideas

### Witnessed and Conformance levels

An earlier draft of this RFC had four levels. Witnessed covered requirements checked on chosen examples through closed laws, and Conformance covered agreement with external oracles such as nix, checked against committed vectors by `ez test`. The appeal was coverage: nearly every requirement could be at some checked level on day one.

In practice both levels are tests under another name, and neither fits Bend. A Witnessed requirement is backed by closed laws, which carry every weakness described in Background while appearing on the same proof gate as real laws, so readers overestimate them. Conformance needs a runner that executes ez against oracle output, which puts a second gate beside the proof gate and makes `ez test`'s test lanes load-bearing. Both levels blur the one distinction the spec exists to draw. Collapsing them into Trusted costs nothing real, because an example-checked claim was never a guarantee, and it makes the remaining Proved requirements mean something.

### Keep converting tests into closed laws

The current direction, moving law-shaped `#|` tests into LAWS/PROOF, has real benefits. It moves checks to compile time, it makes the proof gate the one gate, and each conversion is small and mechanical, which suits agent-driven PRs.

The result is still a test suite checked at a different moment. Converting more of them increases the law count without increasing what is guaranteed, which is why the count has grown while confidence has not. The conversions were a useful inventory of what someone thought mattered, and the first rollout phase uses them exactly that way before retiring them.

### Keep ez test as part of the assurance story

Agents working on ez repeatedly argued that some behaviors, especially IO, could only be established by running tests. `ez test` was built to satisfy that, with caching, parallel lanes, and deadlines, and it does make an unchanged tree fast to re-check. It also became the program that runs the proof gate, which is the part CI relies on.

The argument for its test lanes holds only while IO behavior is unmodeled. Once commands have a planner form, IO decisions are ordinary pure functions and quantified laws cover them for every world, which is strictly more than any test run covers. What remains outside the planner is the interpreter, and a test of the interpreter against a real filesystem still only samples; it does not change the fact that interpreter faithfulness is trusted. So the specification depends on the proof gate and not on any test lane, and the future of the test lanes is a separate decision.

### Prove properties directly over real IO

We could state laws over real IO commands with canned sessions against fake files, as bolt does, without a planner split. This avoids restructuring commands and reuses a technique that already works.

Canned sessions are closed: each fixes one fake filesystem and one transcript. They cannot quantify over worlds, so the frame and reproducibility properties that matter most (EZ-DOC-3, EZ-RES-6, EZ-VEN-3) stay out of reach. The planner split is what turns the fake world from a fixture into a variable.

### Formalize ez separately in Lean

Lean has tactics, a large library, and a mature kernel, so proving a model of ez there would be much less laborious than writing explicit Bend proof terms.

A Lean model would be a second implementation connected to the real code by nothing but good intentions. The value of Bend's approach is that laws are checked against the definitions that actually run. If Bend proof effort blocks a specific requirement, the right response under this spec is to mark it Trusted with a reason, not to prove a copy of it elsewhere.

### A byte-level lock round-trip

The first draft required that rendering a parsed lock reproduces the original bytes. ez never re-renders a parsed lock, and the TOML renderer it uses does no escaping, so that requirement would have forced us to prove a property of a code path nobody runs. Canonical order (EZ-DOC-2) plus parse-after-render (EZ-DOC-1) is what reproducibility actually needs, and we kept those.

## Rollout

The rollout proceeds in phases, each of which leaves the repo consistent.

The first phase writes `SPEC.md` from this RFC, with the proved and pending status of each requirement, and sorts the existing closed laws using the inventory: those that illustrate a requirement are marked with its ID, and the rest are deleted. It tags `pkg/hash_perm` with EZ-HASH-1. This phase changes no behavior and immediately shows how far ez is from its own spec.

The second phase enables the traceability check and adds `mkLint` to ez's flake checks. Pending requirements are reported but do not fail it, so it can go on at once.

The third phase introduces the World model and converts `ez lock` to planner form, then proves EZ-DOC-1 through EZ-DOC-5, EZ-RES-4 through EZ-RES-6 and EZ-RES-8, EZ-VEN-1 through EZ-VEN-3, and EZ-HASH-2, deleting the closed laws each one subsumes. EZ-DOC-3 cannot be proved until the decision on what `ez lock` may read is made, and proving it will require a behavior change to how plain lock gets the file lists of non-vendored git dependencies. `ez lock` goes first because its guarantees are the most important.

Later phases convert `ez add`, `ez fetch`, `ez publish`, the tool commands, and `ez doctor` in the same way, one command per phase, each ending with its requirements proved and its closed laws gone.

The refactoring contract applies from the first phase, since it depends only on law statements and the trust boundary.

## Risks

### Proof effort in Bend

Bend has no tactics or proof search, so quantified laws over strings, TOML documents, and maps require long explicit proofs, and some requirements may cost more to prove than they are worth. `pkg/PROOF.bend` is 2350 lines for 40 laws, most of it the permutation argument behind EZ-HASH-1. With only two levels, the escape hatch is explicit: a requirement that proves too expensive moves to Trusted with a written reason. That is a visible, reviewable weakening rather than a silent one, and we order the work so that structural properties (order independence, framing, idempotence) come before content properties.

### The model can diverge from reality

A law about the World model is only as good as the model. If the model says git reports ancestry one way and real git behaves differently, the proof holds and the tool is still wrong. We accept this, keep the model's fields to what the code actually reads, and list every such assumption in the trust boundary so it is at least visible.

### The spec encodes accidents

Writing requirements from current behavior risks promoting bugs into guarantees. This revision checked every requirement against the code and found several where the code and the README disagree, and several behaviors that look accidental. Each requirement in the first version still needs a deliberate yes from a maintainer, which is why the Draft Status section flags them.

### Headline guarantee requires a behavior change

EZ-DOC-3 does not hold today, and no refactor can make it hold, because `ez lock` reads inputs a clone does not have. Proving it requires deciding what those inputs become and changing ez to match. Until then it stays pending, and the spec says so plainly rather than implying reproducibility the tool does not have.

### Pressure to reintroduce tests

Agents that previously argued for tests will likely argue again, especially for interpreter code. The refactoring contract is the answer: interpreter faithfulness is Trusted, a test does not change that, and a PR that adds tests as a condition of merging is adding a gate the spec does not recognize.

### Checker soundness

Every Proved requirement assumes the Bend checker is sound (EZ-TRUST-1). We cannot fix this from ez. The flake already pins Bend versions and bumps them in their own PRs, which gives us a natural place to re-check the laws against each new checker.

## Future Steps

The same structure applies directly to the sibling libraries. ezjson, eztoml, and ezhttp already describe their laws in terms of external standards (TOML 1.0, RFC 9110, RFC 3986), and a shared traceability rule in bolt would cover all of them with the same two levels. Once ezhttp owns the HTTP laws, ez's EZ-TRUST-5 row points at them.

Once `ez lock` and `ez add` are both in planner form, the World model makes cross-command guarantees expressible, such as "`ez add` followed by `ez lock` on a fresh clone reproduces the lock `ez add` wrote." Those end-to-end statements are the strongest description of what ez is for, and they become provable only once individual commands are pure.

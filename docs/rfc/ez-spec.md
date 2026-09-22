# RFC: A Behavioral Specification for ez

## Draft Status

State: Draft

Items for review:

- [ ] <!-- REVIEW: This draft was written from the README, the PR history, and the Bend LAWS/PROOF conventions. I could not read the contents of the existing LAWS.bend files. Every function name in the law sketches is illustrative and must be mapped to the real code. -->
- [ ] <!-- REVIEW: The requirement list is derived from README behavior. Confirm each one is intended behavior and not an accident of the current implementation. -->
- [ ] <!-- REVIEW: We made lock reproducibility (EZ-DOC-3) the headline guarantee. Confirm this is the property that matters most. -->
- [ ] <!-- REVIEW: The draft deletes closed laws once their requirement has a quantified law, and deletes untagged closed laws outright. Confirm you want them gone rather than kept as non-normative examples. -->
- [ ] <!-- REVIEW: ez test is treated as outside the specification. Decide separately whether it stays as a convenience, shrinks, or is removed. -->
- [ ] <!-- REVIEW: The traceability check is proposed as a bolt rule. Confirm bolt is the right home. -->

---

## Abstract

ez has a growing set of LAWS.bend and PROOF.bend files, but most of them are closed equalities moved over from `#|` tests, so they pin exact outputs for specific inputs rather than stating what ez guarantees. This RFC defines a behavioral specification for ez in which every requirement is either **Proved** by a quantified law or explicitly **Trusted** as an assumption about the environment, with nothing in between. It adds a model of the state each command reads and writes, so that IO behavior can be stated as laws, and a refactoring contract that says exactly which statements a change must preserve.

## Glossary

| Term | Meaning |
| :---- | :---- |
| Ledger | `ez.toml`. The human-edited record of the package, its `[deps.*]`, and its `[tools.*]`. |
| Lock | `ez.lock.toml`. The resolved, machine-written record of every import, rev, and hash. |
| 0x hash | The content hash Bend assigns to a file and its local imports. Names a package on the hub and under `.ez/lib`. |
| narHash | The SRI sha256 of a vendored tree in NAR serialization, as `nix hash path` would report it. |
| World | A value that models everything a command can observe or change: files, git remotes and checkouts, the hub, environment variables, and the cache. |
| Planner | The pure part of a command. It reads a World and returns a plan of effects and an outcome. |
| Interpreter | The thin IO part of a command. It executes a plan against the real system. |
| Law | A claim in LAWS.bend, checked by `bend PROOF.bend`. |
| Quantified law | A law with binders (`for x: T {...}`). It holds for every input of that type. |
| Closed law | A law with no binders. It holds for one specific input, which makes it a unit test checked at compile time. |
| Proved | A requirement backed by a quantified law tagged with its ID. |
| Trusted | A requirement that is assumed, listed in the trust boundary, and checked by nothing. |
| Requirement ID | A stable name such as `EZ-DOC-3` for one entry in this specification. |

## Background

### What ez does

ez is a project manager for Bend 2. Bend already hashes a file and its local imports into a 0x name and serves it from a hub. ez sits on top of that and manages a whole project: it scaffolds projects, vendors git dependencies, resolves the import graph into a lock, fills `BEND_LIB`, builds and runs entries, pins and installs tools, and publishes. It is written entirely in Bend, and it computes the 0x hash a repo would get even when that repo never published, so the import line it writes is the one a published package would have produced.

### How ez proves things today

Bend's verification model splits claims from proofs. LAWS.bend holds the statements, PROOF.bend holds a definition that proves each one, and `bend PROOF.bend` fails until every law is discharged. Proofs are terms built from pattern matching, recursion as induction, and equality rewrites. There are no tactics and no proof search.

ez adopted this model through a series of PRs that moved "law-shaped" equalities out of `#|` test trailers and into LAWS/PROOF across the sha, pkg, lock, git, net, pub, and string/path areas, deleting the trailers once covered. Many of these are closed: the sha PR, for example, moved the empty-string and FIPS `abc` hex claims into laws, and had to add `()` because Bend requires it on a proof with no binders.

Alongside the laws, ez grew `ez test`, a gate that compiles and runs `*/tests/*.bend` with caching and deadlines. It exists mainly because agents working on the repo kept insisting that some properties could only be established by tests. That produced a second, parallel notion of "checked" next to the proof gate.

### Why this leaves us unsure what is proved

A closed law says `f(a) == b` for one `a`, and that has two consequences that pull in opposite directions.

Closed laws are too weak to protect behavior. A refactor that breaks `f` on every input except the witnessed ones still passes `bend PROOF.bend`. The gate gives the feeling of a guarantee without the substance of one, which is exactly the uncertainty we have today.

Closed laws are also too strong to allow change. A witness usually pins the entire output, including parts nobody depends on, such as the exact wording of an error or the order of lines in a report. A correct refactor that changes one of those details breaks the proof, and because nothing records which parts of the output were intended, we cannot tell a regression from an incidental change.

The runtime tests under `ez test` have the same shape, only checked later. Between closed laws and tests, ez has many checks and no statement of what any of them are for.

## Problem Statement

We need a specification that answers two questions for every behavior ez has. What exactly is guaranteed? And is that guarantee proved for all inputs, or assumed? When we change the implementation, the answer must tell us mechanically which statements have to survive. Anything that is neither proved nor honestly labeled as an assumption is noise, because it looks like assurance and is not.

### Goals

- A single document listing every guaranteed behavior of ez, each with a stable requirement ID.
- Exactly two assurance levels: Proved and Trusted.
- An explicit model of the state ez commands observe and change, so that IO behavior can be stated as quantified laws.
- A refactoring contract based only on law statements and the trust boundary.
- Retirement of closed laws as a form of assurance.

### Non-goals

We are not proving Bend itself, git, the hub, nix, or the host filesystem correct; those are trust assumptions and the spec names them. We are not specifying `ez test`, and nothing in this specification depends on it. We are not changing ez's user-facing behavior; where the spec and the current behavior disagree, we record the disagreement and decide separately.

## Proposal

### Overview

The proposal has four parts. A **specification document** (`SPEC.md` at the repo root) lists every requirement with an ID and a level. A **World model** in Bend gives commands a pure form that laws can quantify over. **Law tagging** links every quantified law to the requirement it proves. A **refactoring contract** states which statements a change may touch.

|  |
|:---:|
| <pre>┌──────────┐     ┌───────────────┐          ┌────────────────┐     ┌────────────────┐<br>│ SPEC.md  │────▶│ Requirement   │──Proved─▶│ LAWS.bend      │────▶│ PROOF.bend     │<br>│ (IDs +   │     │ ID + level    │          │ (quantified,   │     │ (bend checks   │<br>│  levels) │     │               │          │  tagged)       │     │  every law)    │<br>└──────────┘     └───────┬───────┘          └────────────────┘     └────────────────┘<br>                         │<br>                      Trusted<br>                         ▼<br>                 ┌───────────────┐<br>                 │ Trust boundary│<br>                 │ (in SPEC.md)  │<br>                 └───────────────┘</pre> |
| Caption: Every requirement ends in either a quantified law that bend checks, or a named assumption. There is no third path. |

### Two levels, and why only two

Every requirement carries exactly one level.

| Level | Meaning | Backed by |
| :---- | :---- | :---- |
| Proved | Holds for every input in the model. | A quantified law in LAWS.bend tagged with the ID. |
| Trusted | Assumed about something ez cannot check from inside Bend. | An entry in the trust boundary table. |

We considered intermediate levels for "checked on examples" and "agrees with an external oracle", and rejected both (see Abandoned Ideas). The short version is that Bend's gate is a proof checker, and anything it checks on a single example is a test wearing a law's syntax. Two levels keep the spec honest: if a claim is not proved for all inputs, we say we are trusting it, and a reader knows exactly how much weight to put on it.

A Proved requirement whose law has not landed yet is marked **pending** in `SPEC.md`. Pending is a status, not a third level: it means "intended to be Proved, not yet guaranteed", and the spec says so plainly. Because `bend PROOF.bend` fails on any undischarged law, a pending requirement's law stays out of LAWS.bend until its proof is written, and the statement lives in `SPEC.md` until then.

### The World model

Laws can only quantify over values, and most of ez's behavior is IO. We close that gap by modeling what a command can see as a value and splitting each command into a pure planner and a thin interpreter.

```
# Illustrative Bend-style types. Names are placeholders.
type World:
  files: Map(Path, Bytes)        # the project checkout
  remotes: Map(Url, Remote)      # git remotes: refs, tags, commits, ancestry
  hub: Map(Hash, Tree)           # what the hub would serve
  env: Map(String, String)       # EZ_TOOL_BIN, XDG_*, ...
  cache: Map(Path, Bytes)        # $XDG_CACHE_HOME/ez

type Plan: List(Effect)          # WriteFile, Link, RunBend, GitFetch, ...

def lock_plan(w: World, a: LockArgs) -> Pair(Plan, Outcome)
```

The planner decides everything: which revs to pin, which files to write and with what bytes, what outcome to report, and what exit status to return. The interpreter executes effects in order and makes no decisions of its own. Requirements are stated over planners, which lets them quantify over worlds, and the interpreter's faithfulness becomes one explicit trust assumption instead of an unstated one scattered across every command.

|  |
|:---:|
| <pre>real system ──read──▶ World ──▶ planner (pure, laws apply) ──▶ Plan ──▶ interpreter ──▶ real system</pre> |
| Caption: All behavior lives in the planner, where laws apply. The interpreter only performs effects and is trusted. |

We do not need to convert every command before the spec is useful. The spec is written against the model from the start, and each command moves to planner form when its requirements move from pending to proved.

### Requirements

The requirements below are the first version of `SPEC.md`. Each one is stated as behavior, not implementation. Law sketches show the intended shape of a quantified law and use placeholder names. Every Proved requirement starts as pending.

#### Hashing (EZ-HASH)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| EZ-HASH-1 | The 0x hash of a tree depends only on its (path, content) pairs, and not on the order in which they are listed or read. | Proved |
| EZ-HASH-2 | NAR serialization of a tree does not depend on directory listing order. | Proved |
| EZ-HASH-3 | A vendored tree lives at `.ez/lib/<h>` where `h` is its 0x hash. | Proved |
| EZ-HASH-4 | ez's 0x hash for an unpublished tree equals the hash `bend --publish` assigns to it. | Trusted |
| EZ-HASH-5 | ez's narHash equals `nix hash path --type sha256 --sri` of the same tree. | Trusted |
| EZ-HASH-6 | The sha256 implementation in `sha/` computes FIPS 180-4 SHA-256. | Trusted |

The split in this group shows how the two levels work together. We cannot prove that ez agrees with nix or with Bend's publisher, because those are other programs, so EZ-HASH-4 and EZ-HASH-5 are Trusted. What we can prove is the structural half of each claim, which is where real bugs live: that neither hash depends on the order a directory happens to be read in. The sha PR already hand-sorts directory names inside `sha/nar.bend`; EZ-HASH-2 turns that implementation detail into a guarantee.

```
law hash_order_free:
  for fs: List(Pair(Path, Bytes)), p: Perm(fs) {
    tree_hash(fs) == tree_hash(permute(fs, p)) : Hash
  }
```

Existing closed laws for the FIPS `abc` vector and the empty string back EZ-HASH-6 only as examples, and a single vector does not establish an implementation. They are removed in the first rollout phase, and EZ-HASH-6 is recorded as what it actually is: trust in a transcription of a published standard.

#### Ledger and lock documents (EZ-DOC)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| EZ-DOC-1 | Parsing a rendered lock yields the lock that was rendered. | Proved |
| EZ-DOC-2 | Rendering is canonical: rendering a parsed lock reproduces the original bytes for any lock ez wrote. | Proved |
| EZ-DOC-3 | `ez lock` output is a function of the ledger and the committed tree. A fresh clone reproduces the lock byte for byte. | Proved |
| EZ-DOC-4 | `ez lock` is idempotent: running it on a world it just produced changes nothing. | Proved |
| EZ-DOC-5 | `ez lock` without `--upgrade` never changes a pinned rev. | Proved |

EZ-DOC-3 is the headline guarantee of the whole tool. The README says `root` and `narHash` exist so that `ez lock` never has to consult anything a clone does not have. As a law, that becomes a frame property: two worlds that agree on the ledger and the committed tree produce the same lock, however else they differ.

```
law lock_reproducible:
  for w1: World, w2: World {
    agree_on_inputs(w1, w2) == True : Bool ->
    lock_bytes(w1) == lock_bytes(w2) : Bytes
  }
```

Defining `agree_on_inputs` is itself part of the specification: it lists exactly which parts of the world `ez lock` is allowed to read. If a future change makes `ez lock` read the cache or query a remote, this law stops proving, which is the regression we want to catch.

#### Resolution (EZ-RES)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| EZ-RES-1 | `ez add` with no ref pins the greatest semver-ish tag; with none, `main`; with no `main`, `master`. | Proved |
| EZ-RES-2 | `ez add` with no entry uses the revision's `[package] entry`, then `[package] bin`, then `main.bend`. | Proved |
| EZ-RES-3 | A target `owner/repo` means `https://github.com/owner/repo`; a git URL is kept; anything else is a path. | Proved |
| EZ-RES-4 | `ez lock --upgrade` never moves a hub dependency. | Proved |
| EZ-RES-5 | An upgraded rev-only dependency moves to the default branch tip only when its pin is an ancestor of that tip, and stays a commit pin. | Proved |
| EZ-RES-6 | `--package NAME` changes only the named dependency or tool. Every other lock entry is unchanged. | Proved |
| EZ-RES-7 | Tags, refs, and ancestry reported by git are accurate. | Trusted |

EZ-RES-1 and EZ-RES-2 are precedence rules, and each becomes a law over every possible list of tags or every possible manifest, not the one or two examples a test would pick. EZ-RES-6 is a frame law, and frame laws are where examples are weakest: an example shows one other entry surviving, and the law shows all of them survive for every lock.

```
law upgrade_one_frames_others:
  for w: World, n: Name, m: Name {
    (n == m) == False : Bool ->
    entry(upgrade_one(w, n), m) == entry(lock_of(w), m) : Maybe(Entry)
  }
```

EZ-RES-5 is proved relative to EZ-RES-7. The law says ez moves a pin only when the model's ancestry relation says so; whether that relation matches the real repository is git's responsibility.

#### Vendoring and source rewriting (EZ-VEN)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| EZ-VEN-1 | The `.gitignore` allowlist names exactly the hashes of dependencies marked `vendor = true`. | Proved |
| EZ-VEN-2 | When an upgrade moves a hash, every import line naming the old hash names the new one afterwards. | Proved |
| EZ-VEN-3 | Import rewriting leaves every line that does not name a moved hash byte-identical. | Proved |
| EZ-VEN-4 | `ez doctor` never writes to the project's source files. | Proved |

EZ-VEN-2 and EZ-VEN-3 together specify rewriting completely: the first says what changes, the second says nothing else does. EZ-VEN-4 is only provable because of the planner split, where it becomes a claim that the plan `doctor` returns contains no `WriteFile` effect under the project root.

#### Tools (EZ-TOOL)

| ID | Requirement | Level |
| :---- | :---- | :---- |
| EZ-TOOL-1 | The link directory is `$EZ_TOOL_BIN`, else `$XDG_BIN_HOME`, else `~/.local/bin`. | Proved |
| EZ-TOOL-2 | A cached checkout and binary are reused only when both correspond to the resolved commit. | Proved |
| EZ-TOOL-3 | A dirty worktree, or a path that is not a checkout, is rebuilt on every run. | Proved |
| EZ-TOOL-4 | A name matching a `[tools.*]` pin resolves to the lock rev; `owner/repo` resolves to remote HEAD. | Proved |
| EZ-TOOL-5 | `ez tool run` exits with the built program's status; any failure before the program runs exits 1. | Proved |
| EZ-TOOL-6 | `ez tool install` and `ez tool upgrade` never run the built binary. | Proved |

EZ-TOOL-5 is stated over the planner's outcome, not over a real process. The planner returns `RunProgram` as its final effect after a successful build and `Exit(1)` on every earlier failure; the interpreter passing the child's status through unchanged is covered by the interpreter trust assumption.

### Outcomes and incidental output

Much of the brittleness in today's closed laws comes from pinning whole outputs. The spec separates output into two kinds.

**Contractual output** is anything a user or a script can reasonably depend on: exit statuses, the bytes of files ez writes (lock, ledger, gitignore, rewritten imports), link paths, and effect plans. Requirements talk only about contractual output.

**Incidental output** is everything else, mainly human-readable progress and error wording. Planners return a structured outcome (for example `Failed{area, reason}`) and a separate renderer turns it into text. Laws are stated over the structured outcome, so a change that rewords a message touches the renderer and no law. One requirement pins the only part of the text that scripts match on:

| ID | Requirement | Level |
| :---- | :---- | :---- |
| EZ-OUT-1 | Every rendered failure begins with `ez: <area>:`, where `area` comes from the outcome. | Proved |

### Retiring closed laws

Closed laws have no standing in this specification. They are not a level, they cannot carry a requirement tag, and nothing in the refactoring contract protects them. We retire them in two steps.

In the first rollout phase, every existing closed law is sorted against the requirement list. A closed law that illustrates a requirement is kept temporarily and marked with the ID it points toward, so the pending requirement has a visible trail. A closed law that fits no requirement is deleted, since it pins behavior nobody has decided to guarantee.

When a requirement's quantified law lands, the closed laws pointing at it are deleted in the same PR. The quantified law strictly subsumes them, and keeping them would reintroduce exactly the brittleness this RFC removes.

<!-- REVIEW: An alternative is keeping closed laws permanently as non-normative examples in a separate EXAMPLES.bend. The draft deletes them to keep one meaning for "law". -->

### Tagging and traceability

Every quantified law carries a comment naming the requirement it proves:

```
# EZ-RES-6
law upgrade_one_frames_others: for w: World, n: Name, m: Name { ... }
```

A check reads `SPEC.md` and every LAWS.bend and fails when:

- A requirement at level Proved, marked proved, has no quantified law tagged with its ID.
- A law is tagged with an ID that does not exist in `SPEC.md`.
- A tagged law has no binders.
- A requirement at level Trusted has no row in the trust boundary table.

It reports, without failing, every requirement still pending. That report is the honest answer to "what does ez prove right now", and it shrinks as proofs land.

bolt already enforces law coverage rules and flags LAWS claims that are neither quantified nor equalities, so the natural home for this check is a bolt rule run through `mkLint`. It depends only on `bend` and file contents, which keeps it inside the proof gate rather than adding a new runner.

### Refactoring contract

This is the rule a contributor or an agent follows when changing ez's implementation. It is short on purpose.

A change to implementation code must keep every Proved law proving without editing its statement in LAWS.bend. The proof in PROOF.bend may be rewritten freely.

A change may not move a requirement from Proved to Trusted. Weakening a guarantee is a behavior change and goes through review as one.

A change that adds a new Trusted row must justify it in the PR description, because every Trusted row is a place where the proof gate stops looking.

A change to a requirement in `SPEC.md` is a behavior change, not a refactor. It is the only way a Proved law's statement may change.

With this in place, "can I change this code and keep the proof?" has a mechanical answer: if `bend PROOF.bend` passes, no tagged statement changed, and the trust boundary did not grow, the change preserved every guarantee ez makes. No test run is required to establish that, and no agent claim that one is needed changes it.

### Trust boundary

These assumptions sit outside the proofs. They are the complete list of Trusted requirements, and naming them keeps the spec honest about what a passing `bend PROOF.bend` means.

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| EZ-TRUST-1 | The Bend checker is sound. | We cannot check it from inside Bend. The BendTT paper and a Lean formalization exist, and the release notes report mismatches between the formalization and the implementation. |
| EZ-TRUST-2 | The interpreter executes plans faithfully. | It makes no decisions and is kept small enough to review line by line. |
| EZ-RES-7 | git reports refs, tags, and ancestry accurately. | The World model takes git's answers as given. |
| EZ-HASH-4 | ez's 0x hash matches `bend --publish`. | The publisher is a separate program. |
| EZ-HASH-5 | ez's narHash matches nix. | nix is a separate program. |
| EZ-HASH-6 | `sha/` implements FIPS 180-4. | A transcription of a published standard; collision resistance is also assumed. |
| EZ-TRUST-3 | The hub serves the tree whose hash was requested. | Bend verifies imports by hash, so this reduces to EZ-HASH-6. |

### How we will know it worked

The spec has done its job when the traceability check passes with no pending requirements in the EZ-DOC and EZ-RES groups, every remaining closed law has been deleted, and a rewrite of `ez lock` internals can be merged on the strength of `bend PROOF.bend` alone, without anyone re-deriving what an old example meant or running a test suite to feel safe.

## Abandoned Ideas

### Witnessed and Conformance levels

An earlier draft of this RFC had four levels. Witnessed covered requirements checked on chosen examples through closed laws, and Conformance covered agreement with external oracles such as nix, checked against committed vectors by `ez test`. The appeal was coverage: nearly every requirement could be at some checked level on day one.

In practice both levels are tests under another name, and neither fits Bend. A Witnessed requirement is backed by closed laws, which carry every weakness described in Background while appearing on the same proof gate as real laws, so readers overestimate them. Conformance needs a runner that executes ez against oracle output, which puts a second gate beside `bend PROOF.bend` and makes `ez test` load-bearing. Both levels blur the one distinction the spec exists to draw. Collapsing them into Trusted costs nothing real, because an example-checked claim was never a guarantee, and it makes the remaining Proved requirements mean something.

### Keep converting tests into closed laws

The current direction, moving law-shaped `#|` tests into LAWS/PROOF, has real benefits. It moves checks to compile time, it makes `bend PROOF.bend` the one gate, and each conversion is small and mechanical, which suits agent-driven PRs.

The result is still a test suite checked at a different moment. Converting more of them increases the law count without increasing what is guaranteed, which is why the count has grown while confidence has not. The conversions were a useful inventory of what someone thought mattered, and the first rollout phase uses them exactly that way before retiring them.

### Keep ez test as part of the assurance story

Agents working on ez repeatedly argued that some behaviors, especially IO, could only be established by running tests. `ez test` was built to satisfy that, with caching, parallel lanes, and deadlines, and it does make an unchanged tree fast to re-check.

The argument holds only while IO behavior is unmodeled. Once commands have a planner form, IO decisions are ordinary pure functions and quantified laws cover them for every world, which is strictly more than any test run covers. What remains outside the planner is the interpreter, and a test of the interpreter against a real filesystem still only samples; it does not change the fact that interpreter faithfulness is trusted. So the specification does not depend on `ez test` at all, and its future is a separate decision.

### Prove properties directly over real IO

We could state laws over real IO commands with canned sessions against fake files, as bolt does, without a planner split. This avoids restructuring commands and reuses a technique that already works.

Canned sessions are closed: each fixes one fake filesystem and one transcript. They cannot quantify over worlds, so the frame and reproducibility properties that matter most (EZ-DOC-3, EZ-RES-6, EZ-VEN-3) stay out of reach. The planner split is what turns the fake world from a fixture into a variable.

### Formalize ez separately in Lean

Lean has tactics, a large library, and a mature kernel, so proving a model of ez there would be much less laborious than writing explicit Bend proof terms.

A Lean model would be a second implementation connected to the real code by nothing but good intentions. The value of Bend's approach is that laws are checked against the definitions that actually run. If Bend proof effort blocks a specific requirement, the right response under this spec is to mark it Trusted with a reason, not to prove a copy of it elsewhere.

## Rollout

The rollout proceeds in phases, each of which leaves the repo consistent.

The first phase writes `SPEC.md` from this RFC, with every Proved requirement marked pending, and sorts the existing closed laws: those that illustrate a requirement are marked with its ID, and the rest are deleted. This phase changes no behavior and immediately shows how far ez is from its own spec.

The second phase enables the traceability check. Pending requirements are reported but do not fail it, so it can go on at once.

The third phase introduces the World model and converts `ez lock` to planner form, then proves EZ-DOC-1 through EZ-DOC-5, EZ-RES-4 through EZ-RES-6, and EZ-HASH-1 and EZ-HASH-2, deleting the closed laws each one subsumes. `ez lock` goes first because its guarantees are the most important and its effects are the simplest.

Later phases convert `ez add`, the tool commands, and `ez doctor` in the same way, one command per phase, each ending with its requirements proved and its closed laws gone.

The refactoring contract applies from the first phase, since it depends only on law statements and the trust boundary.

## Risks

### Proof effort in Bend

Bend has no tactics or proof search, so quantified laws over strings, TOML documents, and maps require long explicit proofs, and some requirements may cost more to prove than they are worth. With only two levels, the escape hatch is explicit: a requirement that proves too expensive moves to Trusted with a written reason. That is a visible, reviewable weakening rather than a silent one, and we order the work so that structural properties (order independence, framing, idempotence) come before content properties.

### The model can diverge from reality

A law about the World model is only as good as the model. If the model says git reports ancestry one way and real git behaves differently, the proof holds and the tool is still wrong. We accept this, keep the model close to the README's description, and list every such assumption in the trust boundary so it is at least visible.

### The spec encodes accidents

Writing requirements from current behavior risks promoting bugs into guarantees. Each requirement in the first version needs a deliberate yes from a maintainer, which is why the Draft Status section flags the full list for review.

### Pressure to reintroduce tests

Agents that previously argued for tests will likely argue again, especially for interpreter code. The refactoring contract is the answer: interpreter faithfulness is Trusted, a test does not change that, and a PR that adds tests as a condition of merging is adding a gate the spec does not recognize.

### Checker soundness

Every Proved requirement assumes the Bend checker is sound (EZ-TRUST-1). We cannot fix this from ez. The flake already pins Bend versions and bumps them in their own PRs, which gives us a natural place to re-check the laws against each new checker.

## Future Steps

The same structure applies directly to the sibling libraries. ezjson, eztoml, and ezhttp already describe their laws in terms of external standards (TOML 1.0, RFC 9110, RFC 3986), and a shared traceability rule in bolt would cover all of them with the same two levels.

Once `ez lock` and `ez add` are both in planner form, the World model makes cross-command guarantees expressible, such as "`ez add` followed by `ez lock` on a fresh clone reproduces the lock `ez add` wrote." Those end-to-end statements are the strongest description of what ez is for, and they become provable only once individual commands are pure.

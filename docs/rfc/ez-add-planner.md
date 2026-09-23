# Design: ez add and ez remove in planner form

## Draft Status

State: Draft. Nothing here changes `ez add` or `ez remove` yet; the work packages below do.

This is the design for the phase after [ez-lock-planner.md](ez-lock-planner.md): converting `ez add` and `ez remove` to pure planners and thin interpreters, then proving the pending rows they touch. It follows the lock design's pattern (a World, a planner that asks or plans, an interpreter that answers and executes) and does not repeat it; read that design's "Summary", "Laziness without losing purity" and "The Plan and the outcome" first. It was written from the code at `0f8f179`, where WP1 of the lock design has landed, and it builds on the shapes WP1 built (see that design's "Update" note) rather than on its sketches. A spike in `pkg/tree/` makes the package walk pure; nothing imports it, so `ez add` behaves exactly as before. [ez-law-inventory.md](ez-law-inventory.md) stays the progress tracker, and `SPEC.md` does not change until a requirement's law lands.

### Open questions

Each question has a recommendation. The first six, and the vendor key, change behavior; the seventh rewords a requirement.

- [ ] <!-- REVIEW: A refused `ez add` lays nothing. Today the tree is laid under BEND_LIB, and `.ez/origins.toml` written, before the name is checked, so a refused add leaves both behind. Recommendation: lay only in a plan that succeeds. A cache fill is not a contractual write, but a refusal whose plan has no effect at all is the simplest EZ-OUT-2 law, and it is the lock's shape. -->
- [ ] <!-- REVIEW: `ez add` stops writing `.ez/origins.toml`. Nothing reads it since the lock's input changes, and `ez lock --upgrade` is decided to stop writing it in WP2. Recommendation: stop, and delete `Git.note`, `Git.origin*`, `Git.but` and their three untagged laws. -->
- [ ] <!-- REVIEW: Where a re-add of a `vendor = true` dependency lays its tree. Today it lays under `$BEND_LIB`, which is not `.ez/lib` in every shell, so the allowlist can name a tree that is not committed; and when the hash moves, the old committed tree stays. Recommendation: lay a vendored tree under `.ez/lib` (`Committed`) and drop the old one, as the upgrade does. -->
- [ ] <!-- REVIEW: `ez remove` of a vendored dependency. Today it drops the allowlist line and leaves `.ez/lib/<hash>` committed, where git keeps tracking it. Recommendation: the plan drops the committed tree, unless another dependency still names that hash. -->
- [ ] <!-- REVIEW: `ez remove` of a name the ledger does not have. Today it re-renders the ledger (dropping comments and unknown keys) and exits 0. Recommendation: refuse with exit 1 and write nothing, as `cargo remove` does. EZ-LED-3 is about the model edit and is unaffected. -->
- [ ] <!-- REVIEW: A package whose modules climb out of the checkout. `K.pkg_of` re-roots it under the trailing components `realpath` reports, which include `.work-<rev>` and the directories above it, so its hash depends on where BEND_LIB is. Recommendation: the pure walk refuses it. -->
- [ ] <!-- REVIEW: `ez add ~/x` records the path with `~/` expanded, so EZ-LED-8's "as it was given" is not quite true. Recommendation: keep the expansion and reword EZ-LED-8 to "as it was given, with a leading `~/` expanded", since a `~/` in the ledger would make the lock read HOME, which EZ-DOC-3 forbids. -->
- [ ] <!-- REVIEW: `vendor = true` is written as a bare boolean, and read either way. Recommendation: yes; see "The vendor key" below. -->
- [ ] <!-- REVIEW: The checkout answer holds the text of every file in the checkout, rather than the planner asking file by file. Recommendation: every file. The NAR hash already reads every file, so it costs no new IO, and it keeps `ez add` to at most three rounds. -->
- [ ] <!-- REVIEW: One package walk. `K.pkg_of` stays IO for `ez publish` until publish is converted. Recommendation: rewrite `K.pkg_of` in the first work package as an ask/answer loop over the pure walk, answered by `F.read`, so the two cannot drift. -->
- [ ] <!-- REVIEW: EZ-LED-8 for the lock. Today every git command anchors its source inside `git/git.bend`, which is interpreter code. Recommendation: every git question a planner asks carries `from = P.anchor(here, url)`, computed by the planner, and the lock's World gains `here` in WP2; the row flips when `ez fetch` does the same. -->
- [ ] <!-- REVIEW: `ez init` in planner form. EZ-LED-6 cannot flip without it. Recommendation: include it here as a small work package; its World is three `Maybe` texts. -->

---

## Summary

`ez add` and `ez remove` become planners in the lock's shape: one World per command holding only what that command reads, a planner that returns either questions or a Plan, and an interpreter that answers and executes. `ez remove` asks nothing: its World is the ledger and `.gitignore`, and its planner is one function. `ez add` asks at most three rounds of questions: what the ref names, then the checkout at that rev. The package walk, which reads files as it goes today, becomes a pure function of the checkout's files; the spike shows it computes the same hash as `K.pkg_of` on five entries of this repository.

With both commands in planner form, EZ-LED-7, EZ-RES-1, EZ-RES-2, EZ-LED-2 and EZ-LED-3 can flip to proved in this phase, and EZ-LED-1, EZ-LED-6, EZ-LED-8, EZ-VEN-1, EZ-HASH-3 and EZ-OUT-2 gain the add and remove halves they are waiting for. None of them looks expensive enough to move to Trusted.

## What the commands read today

| Read | Where | Kept in the World? |
| :---- | :---- | :---- |
| the arguments: target, ref, entry, `--rename`; or the name to remove | `Cmd.add`, `Cmd.remove` | Yes, as `args`. |
| `ez.toml`, or its absence | `load.edit` (`ez/cmd.bend`) | Yes, as `ledger: Maybe<&2, String>`, the shape WP1 gave the lock. |
| `HOME`, for a `~/` target | `add.local` | Yes, as `home`, for `ez add` only. |
| the working directory, through `pwd` | `Git.anchored` | Yes, as `here`, for `ez add` only. |
| `git ls-remote --tags`, `--symref HEAD`, or the named ref | `Git.default.ref`, `Git.resolve` | Yes, as answers. |
| a shallow clone at the rev: its `ez.toml`, the entry's presence, the files the walk reaches, `realpath` of the entry's directory, the NAR hash | `Git.vendor.at`, `K.pkg_of`, `Git.nar` | Yes, as one answer: the NAR hash and every file's text. `realpath` is not needed (see the package walk). |
| `BEND_LIB`, as a path | `Env.lib` | No. Only the interpreter needs it, as for the lock. |
| `.gitignore` | `Up.allowlist` | Yes, as `ignore`, "" when missing. |
| `.ez/origins.toml` | `Git.note` reads it to rewrite it | No. See the second open question. |

Two findings from this reading shape the design, beyond the questions above. `ez add` resolves the ref before it reads the ledger, so a directory with no ledger still asks the remote; the planner reads the ledger first and asks nothing when it will refuse. And `Git.root.rel` recovers the package root relative to the repository by counting components of absolute paths; the pure walk works in checkout-relative paths, so the root it returns is the ledger's `root` directly.

## The World for ez add

```
# add/world.bend
type Args is Data:
  Args{target: String, ref: String, entry: String, rename: String}

# a question, answered by one IO action. `from` is the source as git is to
# read it, which the planner computes as `P.anchor(here, url)`.
type Ask is Data:
  Tags{from: String}                    # git ls-remote --tags <from>
  Head{from: String}                    # git ls-remote --symref <from> HEAD
  Refs{from: String, ref: String}       # ls-remote <from> refs/tags/<ref>{,^{}} refs/heads/<ref>
  Tree{from: String, rev: String}       # shallow fetch at rev, .git removed

type Answer is Data:
  Printed{ok: Bool, text: String}                     # Tags, Head, Refs
  Checkout{nar: String, files: List<&2, T.Source>}    # Tree: NAR hash, every file's text
  Miss{why: String}

type Reply is Data:
  Reply{ask: Ask, answer: Answer}

type World is Data:
  World{args: Args, here: String, home: String, ledger: Maybe<&2, String>,
    ignore: String, replies: List<&2, Reply>}
```

`Tags`, `Head` and `Refs` are the questions WP2 adds for the upgrade, with the same `Printed` answer, so they belong in one shared module (`git/ask.bend`, with its interpreter) rather than in either command. `Tree` is WP2's `Tree` with the package walk taken out of the interpreter: WP2 asks for the checkout at a new rev and walks it in the planner too, which is the lock design's decision that `K.pkg_of` "becomes pure when `ez add` is converted". `T.Source` is the spike's `{at, text}`, which is WP1's `W.Source` again; the shared module should define it once.

The planner asks lazily, as the lock does:

|  |
|:---:|
| <pre>round 1:  World{args, here, home, ledger, ignore, []}   -> Asking [Tags from]      (no ref given)<br>round 2:  ... [Tags: Printed "v1.0 v1.1"]              -> Asking [Tree from rev]  (rev of v1.1)<br>round 3:  ... [Tags, Tree: Checkout{nar, files}]     -> Run Plan{[Lay, Write ez.toml, Write .gitignore, Say], Success}</pre> |
| Caption: `ez add owner/repo`. With no semver-ish tag, round 2 asks `Head`; with a named ref, round 1 asks `Refs`; with a 40-hex ref, round 1 asks `Tree`. |

Before any question the planner checks what needs no answer: a missing ledger (EZ-LED-6), a ledger that does not parse (EZ-LED-1), a target `Tgt.classify` refuses, and a `--rename` that is not a bare key (EZ-LED-7). Each of these is a refusal with no question asked. A clash that the ledger alone decides, a `--rename` or a re-add of a recorded source, is refused before the checkout too; a name that turns on the checkout's `[package] name` is decided after round 3.

A round's cost is small here: at most one `ls-remote` and one clone, and the planner re-runs over at most three replies. We do not need the lock's `wants` and `plan` split, though `add/plan.bend` exposes the same `wants`, `plan` and `step` so the interpreter loop can be shared.

## The World for ez remove

```
# remove/plan.bend
type World is Data:
  World{name: String, ledger: Maybe<&2, String>, ignore: String}
```

`ez remove` asks nothing, so its planner is a function from this World to a Plan, and its interpreter reads two files, calls it, and executes.

## The Plan

Both commands use the `Effect` (`Write`, `Lay`, `Say`), `Place`, `Outcome` (`Success`, `Refused`), `Plan` and `Wrote` that WP1 put in `lock/plan.bend`, with the `writes` and `put` projections its laws use, and `W.Source` from `lock/world.bend`. We move them to a shared `plan/plan.bend` when this phase starts, adding `Drop` (which the lock design's WP2 also needs), so that no command imports another command's planner. `Step` stays per command, since `Asking` names the command's own `Ask`.

| Command | Effects, in order, on success | On refusal |
| :---- | :---- | :---- |
| `ez add` | `Lay` the walked tree, under `Committed` when the recorded dependency is vendored and under `Cache` otherwise; `Write` ez.toml; `Write` `.gitignore` when `I.sync` changes it; `Drop` the old committed tree when a vendored dependency's hash moved; `Say` the tag's rev and the import line | no effect; the reason is in `Refused{why}` |
| `ez remove` | `Write` ez.toml; `Write` `.gitignore` when `I.sync` changes it; `Drop` the committed tree when the dependency was vendored and no other names its hash | no effect; the reason is in `Refused{why}` |

The interpreter exits 0 for `Success` and 1 for `Refused`, as the lock's does.

| Contractual | Incidental |
| :---- | :---- |
| the exit status (EZ-OUT-1) | every `Say` text, including the import line `ez add` prints |
| the bytes written to ez.toml and `.gitignore` | the text of `Refused{why}` |
| that a plan writes a path at all | whether a `Lay` under `Cache` happens |
| the files and manifest of any `Lay` (EZ-HASH-3) | how many rounds `ez add` takes |
| which committed trees are dropped | the scratch directory the interpreter clones into |

EZ-HASH-3 is stated about every `Lay`, cached or committed: whether a cache fill happens is incidental, but what it writes when it happens is not.

### A refused add and the cache

Today a refused `ez add` has already laid the tree under `$BEND_LIB/<hash>` and written `.ez/origins.toml`. In planner form the checkout is read into an answer, in a scratch directory the interpreter removes, and nothing is laid until the plan says so. We recommend keeping that consequence rather than adding a `Lay` to refused plans: the cache fill is not contractual, so EZ-OUT-2 would allow it, but a refused plan with no effect at all is the same law as the lock's (`lock_refusal_writes_nothing`), proved the same way, and a refusal that fills the cache with a package the ledger does not name is a tree nothing will ever read. `.ez/origins.toml` is a contractual write under EZ-OUT-2's wording ("every file it would otherwise write"), which is one more reason to stop writing it.

## The package walk, made pure

`K.pkg_of(entry)` reads each file as the walk reaches it, and asks `realpath` for the entry's directory when a module climbs above it. The spike's `pkg/tree/tree.bend` is the same walk over a list of `{at, text}` files, with three differences:

- A file is looked up in the list. A module that is not there stops the walk, and the package is refused naming it, as `K.pkg_of` dies naming it.
- The walk keeps each found file's text beside its name, so the plan lays exactly the bytes it hashed, and the interpreter writes texts rather than copying files.
- A package that climbs `n` levels re-roots under the last `n` components of the entry's checkout-relative directory, which is what `realpath` returned whenever the climb stayed inside the checkout. A climb past the checkout's top is refused (sixth open question).

The walk is one step iterated under fuel, the shape the lock spike used, and a walk that runs out of fuel with files queued is refused rather than hashed short, which fixes the same silent truncation the lock design found in `resolve`.

What a pure walk enables:

- **EZ-RES-2.** "In the revision" becomes "in the `Checkout` answer's file list", and the entry defaults from the checkout's `ez.toml` text in the same answer through `Git.entry.maybe`, which is already pure. The spike proves the refusal half (`absent_entry_refused`).
- **EZ-HASH-3.** The hash, the laid texts and the manifest all come from one list inside the planner, so "`h` is the 0x hash of the file list whose manifest it writes" is a statement about one `Lay` effect. The spike proves its key step: hashing the found files and hashing the laid files, each weighed by its own text, give the same file list (`walked_named_by_texts`, `walked_manifest_of_texts`).
- **EZ-DOC-3 for upgrades.** WP2's `Tree` answer stops depending on an interpreter walk, so the upgrade's new hash is a planner decision like everything else.

We recommend one walk. The pure walk reports a file it was not given as a question rather than a refusal (a third case beside "here" and "absent"); `ez add`'s interpreter gives it every file, so it never asks, and `K.pkg_of`, which `ez publish` and `pkg/main.bend` still call, becomes a loop that answers those questions with `F.read`. Then there is one implementation of the walk, and a later conversion of `ez publish` changes only its interpreter.

## Laws

`A` is `add/world.bend`, `AP` is `add/plan.bend`, `RP` is `remove/plan.bend`, `P` is the shared `plan/plan.bend`, `T` is the promoted `pkg/tree.bend`. Names that do not exist yet, such as `M.read.ok` or `AP.asks.from`, are law vocabulary the work packages add. `AP.added(w)` is the `M.Dep` the plan records, `AP.ledger.next(w)` and `RP.ledger.next(w)` the ledger model the plan renders (the old one when it refuses), and `AP.answered(w)` is `AP.wants(w) == []`. As in the lock design, a World on which the planner still asks has no effects, so laws about writes need no completeness premise.

### EZ-OUT-2 and EZ-LED-6: refusals, and no ledger

```
# EZ-OUT-2
law add_refusal_writes_nothing:
  for +w: A.World
  for r: {AP.refuses(w) == True{} : Bool}
  {P.writes(AP.plan(w)) == False{} : Bool}

# EZ-OUT-2
law remove_refusal_writes_nothing:
  for +w: RP.World
  for r: {RP.refuses(w) == True{} : Bool}
  {P.writes(RP.plan(w)) == False{} : Bool}

# EZ-LED-6
law add_needs_ledger:
  for +w: A.World
  for none: {A.ledger(w) == None{} : Maybe<&2, String>}
  {AP.refuses(w) == True{} : Bool}

# EZ-LED-6
law add_needs_ledger_asks_nothing:
  for +w: A.World
  for none: {A.ledger(w) == None{} : Maybe<&2, String>}
  {AP.wants(w) == [] : List<&2, A.Ask>}

# EZ-LED-6
law remove_needs_ledger:
  for +w: RP.World
  for none: {RP.ledger(w) == None{} : Maybe<&2, String>}
  {RP.refuses(w) == True{} : Bool}
```

`add_needs_ledger_asks_nothing` says more than the requirement: no remote is contacted. The two existing EZ-LED-6 laws stay. WP1's lock planner already refuses a missing ledger, since its World's ledger is a `Maybe`, and needs only the matching law. Reuses the proof of WP1's `lock_refusal_writes_nothing`: every refusing arm builds `Plan{[], Refused{why}}`. Replaces no trail. Effort: small.

### EZ-LED-1: a ledger that does not parse

```
# EZ-LED-1
law add_refuses_unread:
  for +w: A.World
  for +s: String
  for got: {A.ledger(w) == Some{s} : Maybe<&2, String>}
  for bad: {M.read.ok(M.parse(s)) == False{} : Bool}
  {AP.refuses(w) == True{} : Bool}
```

and the same for `ez remove`. With EZ-OUT-2 these say no guess is written over an unreadable ledger. Reuses `read_refuses_a_problem`, `render_of_unread_is_blank`, which we tag EZ-LED-1 in the same change. Effort: small. The row flips once `ez lock --upgrade` (WP2) and `ez init` have their halves.

### EZ-LED-7: the name

```
# EZ-LED-7
law add_records_named:
  for +w: A.World
  for ok: {AP.refuses(w) == False{} : Bool}
  for done: {AP.answered(w) == True{} : Bool}
  {M.dep.name(AP.added(w))
    == Named.as(A.deps(w), A.url(w), A.rename(w), A.pkg(w), A.fresh(w)) : String}

# EZ-LED-7
law add_refuses_named:
  for +w: A.World
  for done: {AP.answered(w) == True{} : Bool}
  for why: {False{} == String.is_empty(Named.why.as(A.deps(w), AP.name(w), A.url(w),
    A.rename(w))) : Bool}
  {AP.refuses(w) == True{} : Bool}
```

`A.pkg(w)` is `Git.called.maybe` of the checkout's `ez.toml` text, `A.fresh(w)` is `Named.called(place, P.anchor(here, url))`, and `A.url(w)` is the url or the `~/`-expanded path. These two laws turn the eleven existing decision laws into statements about the plan: the first says the plan records the name `Named.as` returns, the second that it refuses whenever `Named.why.as` objects. Both hold by unfolding once the planner is written as a function of those values; the work is keeping it so. Replaces no trail. Effort: small. EZ-LED-7 flips to proved with them.

### EZ-LED-8: path targets

```
# EZ-LED-8
law add_records_as_given:
  for +w: A.World
  for ok: {AP.refuses(w) == False{} : Bool}
  for done: {AP.answered(w) == True{} : Bool}
  {M.source.url(M.source.dep(AP.added(w))) == A.url(w) : String}

# EZ-LED-8
law add_asks_anchored:
  for +w: A.World
  {AP.asks.from(AP.wants(w), P.anchor(A.here(w), A.url(w))) == True{} : Bool}
```

`asks.from(as, f)` says every question names `f` as its source. With the three `P.anchor` laws, these state the add half of the row. The row flips when the lock's questions carry `from` too (eleventh open question) and `ez fetch` is converted. Effort: small.

### EZ-RES-1 and EZ-RES-2: what is pinned, and from which entry

```
# EZ-RES-1
law add_pins_chosen:
  for +w: A.World
  for none: {A.args.ref(w) == "" : String}
  for ok: {AP.refuses(w) == False{} : Bool}
  for done: {AP.answered(w) == True{} : Bool}
  {M.source.tag(M.source.dep(AP.added(w))) == AP.default.ref(w) : String}

# EZ-RES-1
law add_commit_asks_nothing:
  for +w: A.World
  for hex: {Git.is_rev(A.args.ref(w)) == True{} : Bool}
  {AP.resolves(AP.wants(w)) == False{} : Bool}

# EZ-RES-2
law add_entry_default:
  for +w: A.World
  for none: {A.args.entry(w) == "" : String}
  for ok: {AP.refuses(w) == False{} : Bool}
  {M.dep.entry(AP.added(w)) == Git.entry.maybe(A.tree.toml(w)) : String}

# EZ-RES-2
law add_entry_absent:
  for +w: A.World
  for done: {AP.answered(w) == True{} : Bool}
  for ne: {False{} == String.is_empty(AP.entry(w)) : Bool}
  for miss: {None{} == T.look(A.tree.files(w), AP.entry(w)) : Maybe<&2, String>}
  {AP.refuses(w) == True{} : Bool}
```

`AP.default.ref(w)` is `Git.choose` of the `Tags` answer, or `Git.tip.branch` of the `Head` answer when `choose` finds nothing. EZ-RES-1's decisions already have untagged laws in `git/LAWS.bend` (`choose_release`, `choose_prerelease`, `branch_of_symref`, `branch_skips_*`, `exact_*`, `is_rev_*`), which we tag. One is missing: that the release chosen is the greatest, a law over `Git.latest`'s fold that no tag in the list compares greater than the one it returns. Three small laws over `Git.entry.pick` state EZ-RES-2's precedence.

| Law | Reuses | Replaces | Effort |
| :---- | :---- | :---- | :---- |
| EZ-RES-1, command | the `git/LAWS.bend` decision laws | nothing | small |
| EZ-RES-1, greatest | `Git.ord.*` | nothing | medium; key lemma: `ord.ver` is transitive over the tags `latest` has passed |
| EZ-RES-2 | the spike's `absent_entry_refused`, `Git.entry.pick` | nothing | small |

### EZ-HASH-3: a laid tree is named by its manifest

```
# EZ-HASH-3
law add_lays_named:
  for +w: A.World
  {P.lays.named(P.effects(AP.plan(w))) == True{} : Bool}
```

`lays.named(es)` is law vocabulary shared with the lock: for every `Lay{place, h, files}`, the `manifest` entry of `files` is `K.manifest_of(T.sums(rest))` and `h` is `K.hash_of(T.sums(rest))`, where `rest` is every other entry and `T.sums` weighs each by the sha256 of its text. The spike proves the step that is not by construction; the rest is unfolding `K.hash_of`, and a plan that dedups the laid files by path, or refuses when two found files share a path with different texts. The lock's WP1 plan lays `laid(fs, ss)` beside `K.manifest_of(fs)` after `sums.ok(fs, ss)`, so the same law holds of it with `sums.ok` as the lemma.

Reuses the spike's `walked_named_by_texts`. Replaces no trail. Effort: small for `ez add`, small for the lock. The row stays pending until `ez fetch`, which lays trees through `lock/restore.bend`, has its half.

### EZ-VEN-1: the allowlist after add and remove

```
# EZ-VEN-1
law add_allowlist_is_the_ledger:
  for +w: A.World
  {I.hashes(AP.ignore.lines(w)) == I.vended(AP.deps.next(w)) : List<&2, String>}

# EZ-VEN-1
law add_allowlist_keeps_other_lines:
  for +w: A.World
  {I.others(AP.ignore.lines(w)) == I.others(A.ignore.lines(w)) : List<&2, String>}
```

and the same two for `ez remove`. The plan writes `I.sync(deps.next, ignore)` when it differs from `ignore`, exactly what `Up.allowlist` does today; `ignore.lines` is the lines of the file the plan leaves. The line-level laws (`allowlist_is_the_ledger`, `allowlist_keeps_other_lines`) are proved; what is left is `I.sync`'s text layer, which is WP7's lemma (`String.lines` after `String.join`) and is shared, not repeated. Effort: small once WP7's lemma lands. The row flips when add, remove and `ez lock --upgrade` all have their laws.

### EZ-LED-2 and EZ-LED-3: the edits the commands make

```
# EZ-LED-2
law add_keep_idem:
  for m: M.Manifest
  for +d: M.Dep
  {Rend.add.keep(Rend.add.keep(m, d), d) == Rend.add.keep(m, d) : M.Manifest}

# EZ-LED-2
law add_edits_ledger:
  for +w: A.World
  for +m: M.Manifest
  for good: {A.read(w) == M.Good{m} : M.Read}
  for ok: {AP.refuses(w) == False{} : Bool}
  for done: {AP.answered(w) == True{} : Bool}
  {AP.ledger.next(w) == Rend.add.keep(m, AP.added(w)) : M.Manifest}

# EZ-LED-3
law remove_edits_ledger:
  for +w: RP.World
  for +m: M.Manifest
  for good: {RP.read(w) == M.Good{m} : M.Read}
  for ok: {RP.refuses(w) == False{} : Bool}
  {RP.ledger.next(w) == Rend.remove(m, RP.name(w)) : M.Manifest}
```

`add_idem` is about `Rend.add`, but the command calls `Rend.add.keep`, which keeps a vendor bit; `add_keep_idem` is the law the requirement needs. Its key lemma is that `M.find` of `without(ds, n) ++ [d]` for `d` named `n` is `d`. `remove_idem` is already proved and is tagged EZ-LED-3. Effort: medium for `add_keep_idem`, small for the rest. Both rows flip in this phase, relative to EZ-LED-4 for the file's bytes, as the upgrade laws are.

### Trails, and what stays Trusted

No `# toward` trail points at a row this phase proves, so none is deleted. With `.ez/origins.toml` gone, the untagged `origin_read`, `but_drops` and `but_keeps` in `git/LAWS.bend` go with the code they describe. The EZ-LED-4 trails (`render_parse_roundtrip`, `bolt_rev`) stay.

Nothing here should be Trusted. What the laws cannot say is covered by existing rows: that the interpreter reads every file of the checkout and writes each laid text faithfully (EZ-TRUST-2), that git serves the tree at a rev (EZ-RES-7), and that the NAR hash, which the interpreter still computes, matches nix (EZ-HASH-5). Once WP8's pure `Nar.dir` has a pure tree to run on, the `Checkout` answer could carry modes and symlinks and the planner compute the NAR hash too; no requirement needs it this phase.

## The vendor key

`Rend.source` writes `vendor = "true"` through `line`, which quotes every value; the README, and every ledger a person writes, says `vendor = true`. `M.flag` compares the value after eztoml has stripped its quotes, so both spellings already read as true. In TOML they are not the same: `builtins.fromTOML`, which `nix/lib.nix` uses on ez.toml, reads the first as a string. We propose rendering a bare `true` and reading both, which is a one-line change to `Rend.vendor.word` and a new `line.bare`.

For EZ-LED-4 nothing changes in the statement, since the model holds a `Bool` either way. Its eventual proof gains one small lemma, that eztoml's `strip` leaves an unquoted value as it is, the unquoted twin of the lock spike's `strip_quoted`. Existing ledgers keep reading as before, and each is rewritten with the bare spelling the next time `ez add`, `ez remove` or `ez lock --upgrade` renders it, a one-line diff per vendored dependency. ez's own ez.toml has no vendored dependency, so it does not change.

## The spike

`pkg/tree/` is inside the proof gate and changes no behavior: nothing imports `pkg/tree/tree.bend`. Its laws carry no requirement tag, because nothing runs this walk yet.

- `tree.bend` (295 lines): the pure walk, `of(entry, files)`, returning `Walked{hash, root, files}` or `Refused{why}`.
- `LAWS.bend` and `PROOF.bend`: three laws and five lemmas.

| Law | Says | Proof |
| :---- | :---- | :---- |
| `absent_entry_refused` | an entry the checkout does not hold is refused, naming it, with any fuel | the first step stops, a stopped walk stays stopped, and `made` refuses a stop; one rewrite each |
| `walked_named_by_texts` | hashing the found files and hashing the laid files gives the same name | the placed list and the weighed laid list are equal, by induction |
| `walked_manifest_of_texts` | and the same manifest | the same list equality, under `K.manifest_of` |

We also ran the walk, outside the gate, against `K.pkg_of` on this repository, giving the pure walk the text of every file `git ls-files` lists:

```
ez/main.bend         io 0x2160e79d63a9b3f5e151a5f0f2f425f7 root=.         35 files
                   pure 0x2160e79d63a9b3f5e151a5f0f2f425f7 root=.         35 files
pkg/pkg.bend         io 0xa7168d2397b53aa3f11f3d0b949e4a1a root=.          4 files
                   pure 0xa7168d2397b53aa3f11f3d0b949e4a1a root=.          4 files
lock/lock.bend       io 0xe7b933bda3ab04d49220a988a598e7ee root=.         10 files
                   pure 0xe7b933bda3ab04d49220a988a598e7ee root=.         10 files
manifest/LAWS.bend   io 0xacce45a1ad6a67a1a363b7219cf1dc13 root=manifest   5 files
                   pure 0xacce45a1ad6a67a1a363b7219cf1dc13 root=manifest   5 files
tests/cli.bend       io 0x6336eb2017dddccca7c2cdde7560dede root=.          5 files
                   pure 0x6336eb2017dddccca7c2cdde7560dede root=.          5 files
ez/nothere.bend    pure refused; io died, both naming the file
```

`ez/main.bend` and `tests/cli.bend` climb through `..`, so the re-rooting without `realpath` is exercised. The evidence for the gate:

```
$ BEND_LIB=$PWD/.ez/lib bend pkg/tree/PROOF.bend
All terms check.
$ BEND_LIB=$PWD/.ez/lib bin/ez.bin prove
PASS: 11 / 11
$ bolt.bin --gpu off
0 errors, 378 warnings        (374 before the spike; the new ones are L001, defs no law names)
```

What the spike does not tell us: it has no planner around the walk, no interpreter, and no timing. The interpreter running the walk from a 101-file list needed the compiled binary; `bend try.bend` overflowed the interpreter's stack, which `bin/ez.bin` does not use. We have not measured a checkout much larger than this repository.

## Work packages

|  |
|:---:|
| <pre>  WP1 (landed) -> A0 shared plan, git asks, pure walk --+--> A1 remove --+<br>                                                      |               +--> A7 flips<br>  WP2 (lock) ...... shares git/ask.bend ...............+--> A2 add -----+<br>                                                                      ^<br>  A3 vendor bare      A4 init      A5 RES-1 greatest      A6 LED-2 ---+<br>  (independent)       (after A0)   (independent)          (independent)</pre> |
| Caption: An arrow means "starts after". A3, A5 and A6 can start at once. A2 needs WP7's text lemma only for its EZ-VEN-1 laws. |

| WP | Scope | Needs | Effort |
| :---- | :---- | :---- | :---- |
| A0 | Move WP1's `Effect`, `Place`, `Plan`, `Outcome`, `Wrote`, `writes`, `put` and `Source` to `plan/plan.bend`, with `Drop` and `lays.named`. Create `git/ask.bend` (the `Tags`, `Head`, `Refs`, `Tree` questions, `Printed` and `Checkout`, and their interpreter) unless WP2 has. Promote the spike to `pkg/tree.bend` with the "not given" case, and rewrite `K.pkg_of` as a loop over it. No behavior change except the climb-out refusal. | nothing; WP1 has landed | medium |
| A1 | `ez remove` in planner form: `remove/plan.bend`, its interpreter, the decided changes (drop the committed tree, refuse an absent name). Lands EZ-OUT-2, EZ-LED-6, EZ-LED-1 and EZ-VEN-1 laws for remove, and tags `remove_idem` EZ-LED-3. | A0 | small |
| A2 | `ez add` in planner form: `add/world.bend`, `add/plan.bend`, `add/run.bend`; delete `Git.vendor*`, `Git.note`, `Git.default.ref`'s IO and the add half of `ez/cmd.bend`. The decided changes. Lands the add laws for EZ-OUT-2, EZ-LED-1, 2, 6, 7, 8, EZ-RES-1, EZ-RES-2, EZ-HASH-3 and EZ-VEN-1. | A0, A6 for EZ-LED-2, WP7's lemma for EZ-VEN-1's text layer | large |
| A3 | Render `vendor = true` bare; a law that a bare `true` reads as true. | nothing | small |
| A4 | `ez init` in planner form: World of the ledger, `.gitignore` and entry texts as `Maybe`; `init_keeps_ledger` becomes a plan law. | A0 | small |
| A5 | EZ-RES-1's missing law: the release `Git.choose` returns is the greatest. | nothing | medium |
| A6 | EZ-LED-2's model law `add_keep_idem`. | nothing | medium |
| A7 | Flip the rows whose halves have all landed, update `SPEC.md` and the inventory: EZ-LED-2, EZ-LED-3, EZ-LED-7, EZ-RES-1, EZ-RES-2 after A1, A2, A5, A6; EZ-LED-1, EZ-LED-6, EZ-VEN-1 once WP2 and A4 are in too. EZ-LED-8, EZ-HASH-3 and EZ-OUT-2 stay pending until `ez fetch` is converted, and say so under "Left to prove". | the rest | small |

A0 is the only package that touches modules WP1 and WP2 own (`lock/plan.bend`'s types, and `git/ask.bend` if WP2 got there first); it moves them and changes no statement, so it is a refactor under the contract. A1 and A2 are the only packages that change behavior, and each lists its changes in its PR description. A2 can run alongside WP2 once A0 lands, since the two share only `git/ask.bend`.

## Risks

**A large checkout in memory.** The `Checkout` answer holds every file's text. The NAR hash reads the same files today, one at a time; holding them all at once is new. We will measure `ez add` on the largest dependency this repository has before A2 lands, and fall back to answering only `.bend` files and the foreign bodies the walk names, in one more round, if it matters.

**Laying texts, not copying bytes.** The interpreter writes each file's text instead of `cp`. A file that is not valid UTF-8 would be written back differently, but its hash would already differ from `bend --publish`'s in the same way, since both hash the decoded text (EZ-HASH-6), and WP1 lays cache fills the same way.

**Two conversions touching `git/`.** WP2 and A2 both move IO out of `git/git.bend`. A0 settles the shared questions first, so the two only delete disjoint code afterwards.

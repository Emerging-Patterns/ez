# Design: ez lock in planner form

## Draft Status

State: Accepted. Nothing here changes `ez lock` yet; the work packages below do.

**Update:** WP1 has landed. Plain `ez lock` runs the planner in `lock/world.bend`, `lock/plan.bend` and `lock/run.bend`, the spike in `lock/world/` is deleted, and its laws are restated over that planner in `lock/LAWS.bend`. Where the code differs from the sketches below: an `Ask` carries the hub a hub package is served from, so the interpreter never parses the ledger; the World's ledger is `Maybe<&2, String>`, so a missing ez.toml is refused by the planner (EZ-LED-6); `Outcome`'s success is `Success{}`, since Base owns `Done`; a refused plan has no effect at all and its reason is in `Refused{why}`; and a `Lay` is built from the planner's verdict, so only a checked tree is laid, and only by a lock that succeeds. Progress is tracked in [ez-law-inventory.md](ez-law-inventory.md) under "Phase three progress".

**Update:** WP2 has landed. `ez lock --upgrade` runs in the same planner: `lock/up.bend` decides the upgrade from its own questions, `Up.run`, `Pin.upgrade` and `ez/upgrade.bend` are deleted, and `lock_refusal_writes_nothing` holds of every World, so it is tagged EZ-OUT-2. Where the code differs from the sketches below: the upgrade's questions and answers are their own types in `lock/up.bend` (`Up.Ask`, `Up.Answer`), held in a fifth World field, `ups`, and `Asking` carries both kinds; `Inputs` holds the ledger the lock is made from, read (`M.Read`), and `stop`, the upgrade's refusal, and its listing is the committed sources as the upgrade rewrites them (`W.listing.of`); `P.ledger.next` is the model the upgrade renders (`Up.next.model`), while the lock is made from that text read back (`Up.next.read`), so a later plain lock reads what this one did; a checkout at the rev a dependency moves to answers the lock's package question for the new hash (`Up.Laid`), so the tree is not cloned twice, and it is laid under `.ez/lib` when the ledger the upgrade leaves vendors that hash and under `$BEND_LIB` otherwise; the hub is asked about a hash only after a pin advances; `U.judge` gets the real agreement of the pinned commit's checkout, and `False` for a commit that moved, which `judge.move` does not read; the plan's lines a person is told (`Say`, on stdout) come first; and the sources are rewritten once, by the plan, not on every round of questions, which is what kept the demand loop's cost down (see the inventory). The interpreter still exits 1 without writing when git cannot be asked at all (a clone or a `merge-base` that fails), since no effect has run by then.

This is the design for phase three of [ez-spec.md](ez-spec.md): converting `ez lock` to a pure planner and a thin interpreter, then proving EZ-DOC-1 through EZ-DOC-5, EZ-RES-4 through EZ-RES-6 and EZ-RES-8, EZ-VEN-1 through EZ-VEN-3, and EZ-HASH-2. It was written from the code at `bec3435`. A spike in `lock/world/` checks the riskiest parts against bend 2.0.25; nothing imports it, so `ez lock` behaves exactly as before. [ez-law-inventory.md](ez-law-inventory.md) stays the progress tracker, and `SPEC.md` does not change until a requirement's law lands.

### Open questions

Every question below was the maintainer's, and each is resolved. The maintainer accepted every recommendation, and made "a refused command writes nothing" a requirement, EZ-OUT-2, for every command. The spec's changes are recorded in [ez-spec.md](ez-spec.md) and `SPEC.md`.

- [x] <!-- REVIEW (resolved): Local imports. The planner takes the hub imports of every tracked `.bend` file and follows no local import, so an untracked file a tracked one imports never reaches the lock. This is a decided behavior change. -->
- [x] <!-- REVIEW (resolved): Trees under BEND_LIB. The planner checks every package's manifest against its `0x` name, and judges a tree read from BEND_LIB as the same bytes cloned at the ledger rev and weighed to the ledger's narHash. We accept that a wrong narHash still locks in a working checkout and is refused on a fresh clone, since the lock's bytes agree whenever both succeed. -->
- [x] <!-- REVIEW (resolved): EZ-DOC-5 now reads "`ez lock` without `--upgrade` never writes ez.toml, and records every dependency's and tool's pin exactly as ez.toml has it." -->
- [x] <!-- REVIEW (resolved): EZ-RES-6 now says `--package NAME` asks the remote to resolve only the named entry, where resolving is asking for refs, the default branch, ancestry, or a checkout at a new rev. Fetching an unchanged tree at its ledger rev is not resolving. -->
- [x] <!-- REVIEW (resolved): The phase-three upgrade laws are stated over the ledger model the plan renders, and hold of ez.toml's bytes relative to EZ-LED-4. `SPEC.md` records the dependency under "Left to prove". -->
- [x] <!-- REVIEW (resolved): EZ-DOC-1 takes route (a): the whole text round trip is proved in ez against the pinned eztoml v0.1.0 reader, sections first, then text. -->
- [x] <!-- REVIEW (resolved): The planner refuses to write a lock that is not `lockable`, so EZ-DOC-1's precondition is behavior and not an assumption. This is a decided behavior change. -->
- [x] <!-- REVIEW (resolved): "A command that refuses writes nothing" is a requirement, EZ-OUT-2, stated for every command. `ez lock` meets it in this phase, and each other command when it is converted. -->
- [x] <!-- REVIEW (resolved): `ez lock --upgrade` stops writing `.ez/origins.toml`. This is a decided behavior change. -->
- [x] <!-- REVIEW (resolved): `K.pkg_of` stays in the interpreter for new upgrade checkouts in this phase, under EZ-TRUST-2, and becomes pure when `ez add` is converted. -->
- [x] <!-- REVIEW (resolved): An upgrade lays a moved vendored tree under `.ez/lib` and any other moved tree under `$BEND_LIB`. This is a decided behavior change. -->
- [x] <!-- REVIEW (resolved): Each command has its own World, holding only what that command reads. -->

---

## Summary

`ez lock` becomes three pieces. A **World** is a value holding everything the lock reads: the ledger's text, the committed `.bend` files, and one answer per question the planner asked. A **planner** is a pure function from a World to a **Step**: either a list of questions it still needs answered, or a **Plan** of effects and an outcome. An **interpreter** reads the ledger and the listing, then loops: it runs the planner, answers its questions by IO, adds the answers to the World, and runs it again, until the planner returns a Plan, which the interpreter executes.

|  |
|:---:|
| <pre>          +---------------------- asks ------------------------+<br>          |                                                    |<br>          v                                                    |<br>  +---------------+   World    +-------------------+   Step    |<br>  | interpreter   | ---------> | planner (pure)    | --------> +<br>  | reads, asks,  |            |  inputs, accept,  |           |<br>  | executes      | <--------- |  walk, upgrade,   |    Plan   |<br>  +---------------+    Plan    |  render           | <---------+<br>          |                    +-------------------+<br>          v<br>  files written, trees laid, exit status</pre> |
| Caption: The planner decides everything, including what to ask next. The interpreter only reads, asks and executes, and is covered by EZ-TRUST-2. |

The spike shows this shape is cheap to prove things about. The headline guarantee, EZ-DOC-3, costs little once the planner is written to depend on a World only through a projection `inputs`, and the spike proves the part of it that is not true by construction: a working checkout, whose trees come from BEND_LIB, locks exactly as a fresh clone, which clones and weighs every tree. The most expensive requirement is EZ-DOC-1, the lock's text round trip through eztoml's reader; the spike proved its three hardest string lemmas, so we estimate it large but not blocked. No requirement in this phase looks expensive enough to move to Trusted.

## What ez lock reads today

Recent changes already narrowed plain `ez lock` to the inputs EZ-DOC-3 allows. Reading the code at `bec3435`:

| Read | Where | Kept in the World? |
| :---- | :---- | :---- |
| `ez.toml`, three times | `Pin.need` (`ez/pin.bend:417`), `Lock.lock.at` (`lock/lock.bend:916`) | Yes, once, as `ledger`. |
| `git ls-files -- '*.bend'` | `sources` (`ez/cmd.bend:215`) | Yes, as `listing`, with each file's text. |
| every local file a tracked file imports, tracked or not | `root.found` (`lock/lock.bend:563`) | No. See the first decision under "Open questions". |
| `$BEND_LIB/<hash>/manifest` and its files, per git package | `read.git` (`lock/lock.bend:364`) | Yes, as an answer, marked as read from BEND_LIB. |
| a clone at the ledger rev, when the tree is missing | `fetch.git` (`lock/lock.bend:304`) | Yes, as an answer, marked as cloned with the narHash it weighed. |
| the hub's manifest and files, per hub package | `read.hub` (`lock/lock.bend:404`) | Yes, as an answer, marked as served. |
| `$BEND_LIB` itself, as a path | `lib` (`lock/lock.bend:902`) | No. Only the interpreter needs the path. |
| `ez.lock.toml`, `.ez/origins.toml`, `BEND_HUB`, `bend version` | nowhere | No. |

Under `--upgrade` it also reads what the remote says about refs, the default branch and ancestry, checkouts at new revs, `.gitignore`, and every `.bend` file `find` lists outside `.ez` and `.git` (`ez/upgrade.bend:400`), and it asks the hub whether it holds a moved hash (`hub.check`, `ez/upgrade.bend:105`).

Three findings from this reading shape the design, beyond the decisions above:

- A package under BEND_LIB is never checked against its own name, so a stale or edited tree there can reach the lock. The planner checks every package's manifest against its `0x` name, whatever it came from.
- Both walks stop silently when their fuel runs out: `resolve` and `roots` return what they have (`lock/lock.bend:537, 637`). With fuel at 100000 this is unlikely, but a truncated lock written with exit 0 is the failure EZ-DOC-3 exists to prevent. The planner refuses when fuel runs out with work left.
- In the upgrade, `U.judge` is always called with its agreement bit set to true, so its `Drift` arm is dead and drift is decided later by `confirmed` (`ez/upgrade.bend:159`). The planner calls `U.judge` with the real bit, which is what makes EZ-RES-8 a statement about `U.judge`.

## The World

The types below are the proposal for `lock/world.bend`. The part for plain `ez lock` is what the spike implements (`lock/world/world.bend`); the upgrade questions are added in the second work package.

```
# the flags: `--upgrade`, and the name `--package` gave, "" for none
type Args is Data:
  Args{upgrade: Bool, only: String}

# one committed `.bend` file: its path and its text
type Source is Data:
  Source{at: String, text: String}

# what `git ls-files '*.bend'` answered, or why git could not list
type Listing is Data:
  Listed{files: List<&2, Source>}
  Unlisted{why: String}

# how the interpreter came by a package's bytes
type How is Data:
  Lib{}                 # already under BEND_LIB: vendored, or left by an earlier lock
  Clone{nar: String}    # cloned at the ledger rev now, with the narHash it weighed
  Served{}              # from the hub

# a question the planner asks. Each is answered by one IO action.
type Ask is Data:
  Pkg{hash: String, src: L.Src}                    # a package's manifest and file texts
  Refs{url: String, ref: String}                   # `git ls-remote url refs/tags/<ref> ...`
  Head{url: String}                                # `git ls-remote --symref url HEAD`
  Tags{url: String}                                # `git ls-remote --tags url`, for a tool with no tag
  Above{url: String, pin: String, tip: String}     # `merge-base --is-ancestor pin tip`
  Tree{url: String, rev: String, entry: String}    # a clone at rev: narHash, root, the package its entry reaches
  Weigh{url: String, rev: String}                  # a clone at rev, narHash only, for a tool
  HubHas{hash: String}                             # the hub's manifest for a moved hash
  Ignore{}                                         # `.gitignore`, "" when missing
  Sources{}                                        # every `.bend` file outside `.ez` and `.git`, with its text

# the answer to one question. Git's output is kept as it was printed, so
# reading it is the planner's decision and not the interpreter's.
type Answer is Data:
  Got{how: How, manifest: String, srcs: List<&2, String>}          # Pkg
  Printed{ok: Bool, text: String}                                  # Refs, Head, Tags
  Onward{yes: Bool}                                                # Above
  Checkout{nar: String, root: String, manifest: String, srcs: List<&2, String>}  # Tree
  Weighed{nar: String}                                             # Weigh
  HubSaid{got: Web.Got}                                            # HubHas
  Text{text: String}                                               # Ignore
  Files{files: List<&2, Source>}                                   # Sources
  Miss{why: String}                                                # any question IO could not answer

type Reply is Data:
  Reply{ask: Ask, answer: Answer}

# everything `ez lock` reads
type World is Data:
  World{args: Args, ledger: String, listing: Listing, replies: List<&2, Reply>}
```

Every field is something the code reads today or reads under a decided change, and nothing else is in it. There is no field for the environment, the clock, `bend version`, the old lock, `.ez/origins.toml` or untracked files; the lock does not read them, so there is nothing for a law to quantify over. BEND_LIB's path is not a field either: the planner never needs it, because an answer says whether it came from there and a `Lay` effect names a place, not a path.

### How the interpreter gathers each field

| Field or question | Gathered by | When |
| :---- | :---- | :---- |
| `args` | the command line | always |
| `ledger` | `F.read("ez.toml")`, a missing file read as "" | always |
| `listing` | `git -c core.quotepath=off ls-files -- '*.bend'`, then `F.read` of each | always |
| `Pkg` for a hub source | GET `<hub>/<hash>/manifest`, then each file it names | for each hash the planner reaches |
| `Pkg` for a git source | `$BEND_LIB/<hash>` when it holds a manifest (`Lib`), else a shallow clone at the ledger rev, `.git` removed, `Git.nar`, `K.pkg_of(entry)` (`Clone{nar}`) | for each hash the planner reaches |
| `Refs`, `Head`, `Tags` | `git ls-remote`, output kept | `--upgrade`, selected git pins |
| `Above` | the blobless bare clone and `merge-base` of `Git.descendant.at` | `--upgrade`, after `Refs` or `Head` answered with a different commit |
| `Tree` | `Git.vendor.at` without laying or noting anything: clone, `.git` removed, `Git.nar`, `K.pkg_of(entry)`, `Git.root.rel` | `--upgrade`, for a commit the planner will pin or confirm |
| `Weigh` | `Git.weigh` | `--upgrade`, tools |
| `HubHas` | `Web.fetch` of the moved hash's manifest | `--upgrade`, after a hash moved |
| `Ignore` | `F.read(".gitignore")` | `--upgrade` |
| `Sources` | `find . -name '*.bend' -not -path '*/.ez/*' -not -path '*/.git/*'`, then `F.read` of each | `--upgrade`, only after a hash moved |

The interpreter reads a package's files in the order its manifest names them. That reading of the manifest is a parse in IO, but it only decides what to fetch: the planner parses the same manifest again and checks every text against its sum, so a wrong parse is a refusal, never a wrong lock. The same holds for `K.pkg_of` on a plain lock's clone, since the planner checks the result against the ledger's hash. It does not hold for `Tree` under `--upgrade`, where the walk's result is the new hash; see the decision on the package walk under "Open questions".

### Laziness without losing purity

A World cannot hold every answer up front. Which packages the lock needs is known only after reading the packages it already reached, and which commit to check out is known only after the remote answered. We model this as a demand loop rather than as functions inside the World:

|  |
|:---:|
| <pre>round 1:  World{ledger, listing, []}             -> Asking [Pkg 0xb]<br>round 2:  World{..., [0xb: Got]}                  -> Asking [Pkg 0xa]     (0xb imports 0xa)<br>round 3:  World{..., [0xb: Got, 0xa: Got]}       -> Run Plan{[Write ez.lock.toml], Done}</pre> |
| Caption: The spike ran exactly this sequence on a two-package sample: ask, ask, lock. |

The planner is a total function of the World. On a World that lacks an answer it needs, it returns that question; it never guesses. The loop is the interpreter's, runs under fuel, and each round adds at least one answer, since the planner never asks what the World already answers. Laws quantify over every World, and a law about what `ez lock` writes is a law about the Worlds on which the planner returns a Plan.

Re-running the planner every round re-verifies every package each round, and verification is a SHA-256 of every file. A plain lock takes one round more than the depth of the import graph, so we split the planner in two: `P.wants(w)` scans answered packages for imports without verifying them and returns the questions still open, and `P.plan(w)` verifies once. The interpreter loops on `wants` until it is empty, then calls `plan`. A law ties them: when `wants(w)` is empty, `plan(w)` asks nothing. A body that fails verification may cause `wants` to ask for more than needed, which costs a fetch and changes nothing, because `plan` refuses it.

## The Plan and the outcome

```
# where a package is laid: `.ez/lib`, which is committed for a vendored
# dependency, or `$BEND_LIB`, which is a cache
type Place is Data:
  Committed{}
  Cache{}

type Effect is Data:
  Write{path: String, text: String}                            # ez.lock.toml, ez.toml, .gitignore, a source
  Lay{place: Place, hash: String, files: List<&2, Source>}      # a package's files, and its manifest beside them
  Drop{hash: String}                                           # `.ez/lib/<hash>`, a committed tree that moved
  Say{text: String}                                            # a progress line

type Outcome is Data:
  Done{}
  Refused{why: String}

type Plan is Data:
  Plan{effects: List<&2, Effect>, outcome: Outcome}

type Step is Data:
  Asking{asks: List<&2, Ask>}
  Run{plan: Plan}
```

The interpreter executes the effects in order, stopping with exit 1 at the first write that fails, and then exits 0 for `Done` and 1 for `Refused`. A refused plan has no `Write`, `Lay` or `Drop` effect, which is EZ-OUT-2 for `ez lock`:

```
# EZ-OUT-2
law lock_refusal_writes_nothing:
  for +w: W.World
  for r: {P.refuses(w) == True{} : Bool}
  {P.writes(P.plan(w)) == False{} : Bool}
```

It is small: every arm of the planner that refuses builds its plan from `Say` effects alone. WP1 lands it for a plain lock and WP2 for `--upgrade`.

The plan's effects come in this order: lay new trees, write ez.toml once (dependencies and tools together, where today `Up.run` and `Pin.upgrade` each write it), write `.gitignore`, rewrite sources, drop old committed trees, write ez.lock.toml. A plain lock's plan is at most one `Lay` per cloned tree (a cache fill) and the lock's `Write`.

| Contractual | Incidental |
| :---- | :---- |
| the exit status (EZ-OUT-1) | every `Say` text |
| the bytes of each `Write` to ez.lock.toml, ez.toml, `.gitignore` and sources | the text of `Refused{why}` |
| that a plan writes a path at all | the order of `Say` effects |
| the files and manifest of a `Lay` under `Committed` (EZ-HASH-3) | whether a `Lay` under `Cache` happens |
| which committed trees are dropped | how many rounds the loop takes |

Laws mention only the left column. Refusal is stated as `P.refuses(w) == True{}`, never as a message, so rewording a refusal touches no law.

## Planner, interpreter and module layout

```
# lock/world.bend: the types above, and what the lock may depend on
def inputs(w: World) -> Inputs
def accept(orgs: List<&2, L.Origin>, hash: String, answer: Answer) -> Verdict

# lock/plan.bend: the planner, pure
def wants(w: World) -> List<&2, Ask>
def plan(w: World) -> Plan
def step(w: World) -> Step                      # Asking when wants(w) is not empty, else Run
def put(w: World, path: String) -> Wrote        # Kept{} or Put{text}: the bytes a plan writes to a path
def refuses(w: World) -> Bool
def ledger.next(w: World) -> M.Read             # the ledger model the plan renders into ez.toml

# lock/up.bend: the upgrade's decisions, pure (from ez/upgrade.bend and ez/pin.bend)
def deps(w: World, orgs, ds: List<&2, M.Dep>) -> Up.Out
def tools(w: World, ts: List<&2, M.Tool>) -> Up.Bunch

# lock/run.bend: the interpreter
def answer(ask: Ask) -> IO(Answer)
def exec(e: Effect) -> IO(Unit)
def run(args: Args) -> IO(Unit)                 # read, loop on wants, plan, execute
```

`ez/cmd.bend`'s `lock` calls `Run.run(Args{up, name})` and nothing else.

How much of today's code moves unchanged:

| Code | Lines | Fate |
| :---- | ----: | :---- |
| `lock/lock.bend` pure half: `Src`, `Pack`, `Origin`, `ledger.read`, `origin`, `known`, `has`, `specs`, `kids`, `manifest.files`, `nar.why`, `render.tools`, `doc`, `pack.sort`, and the readers `packs`, `pack_of`, `lock.hub` | about 465 of 929 | unchanged; the planner and `restore.bend` both use it |
| `lock/lock.bend` IO half: `files.judge`, `fetch.*`, `disk.*`, `read.*`, `resolve.*`, `root.*`, `roots`, `lib`, `lock.at` | about 460 | the checks become `accept` (planner); the reads become `answer` (interpreter); the two continuation-passing walks become one pure walk |
| `manifest/upgrade.bend` (`U.aim`, `U.judge`, `U.agree`, `U.retarget`, `U.reimport.many`) and `manifest/ignore.bend` (`I.sync`) | 576 | unchanged; the upgrade planner calls them |
| `ez/upgrade.bend` | 532 | `Done`, `Out`, `join`, `swap.of`, `swap.hash` move to `lock/up.bend` unchanged; `walk`, `one`, `follow`, `forward`, `ask`, `judged`, `confirm`, `advanced` become pure functions of replies; `go.out` and the writers become effects |
| `ez/pin.bend` | 424 | `set`, `join`, `gap`, `gaps` move unchanged; the IO walk becomes pure, like the dependency walk |
| `git/git.bend` pure parsers `rows`, `exact`, `tip.rev`, `tip.branch`, `choose` | | unchanged; the planner reads `Printed` answers with them |

The walk is written as one step that does not recurse, iterated under fuel (`lock/world/world.bend`, `step` and `walk`). The IO walks use continuation passing because an IO def cannot branch on a value and recurse in the branch; a pure planner does not need it, and a step iterated under fuel turns every invariant into one lemma about one step plus an induction on the fuel. The spike's `walk_pins_ledger_sources` is proved exactly that way.

## Laws

Every law below is stated over the planner. Names that do not exist yet are the ones in the layout above: `P` is `lock/plan.bend`, `W` is `lock/world.bend`. A World on which the planner still asks has no effects, so a law about what the plan writes holds on it trivially, and we add no premise that the World is complete unless the law needs one.

### EZ-DOC-3: reproducible from committed inputs

```
# EZ-DOC-3
law lock_reproducible:
  for w1: W.World
  for w2: W.World
  for e: {W.inputs(w1) == W.inputs(w2) : W.Inputs}
  {P.put(w1, "ez.lock.toml") == P.put(w2, "ez.lock.toml") : P.Wrote}

# EZ-DOC-3
law clone_reproduces:
  for +w: W.World
  {P.put(W.reclone(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}
```

`inputs` is the ledger, the listing, and every reply with its answer replaced by the planner's verdict on it. A verdict is the files and texts once every check passed, or the refusal; how the bytes arrived is not in it. `reclone` replaces every answer read from BEND_LIB with the same bytes cloned and weighed to the ledger's narHash, which is the World a fresh clone produces. Together they say: the lock depends on nothing but the ledger, the committed sources and checked package bytes, and a working checkout locks as a fresh clone does.

What stays trusted is that a fresh clone's interpreter gets the same bytes: that git serves the same tree at a rev (EZ-RES-7), that the hub serves what was published (EZ-TRUST-3), and that SHA-256 does not collide (EZ-HASH-6). All three are already Trusted rows.

Reuses `lock/LAWS.bend nar_why_agrees`. Replaces no trail. Effort: small. Both laws are proved in the spike for its planner (`plan_frame`, `clone_reproduces`); the first holds by construction because the planner is written as `plan.of(inputs(w))`, and the second by induction over the replies with one lemma per kind of answer. The work is keeping the planner factored through `inputs` as it grows the upgrade.

### EZ-DOC-5: a plain lock keeps every pin

```
# EZ-DOC-5
law plain_lock_keeps_ledger:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.put(w, "ez.toml") == P.Kept{} : P.Wrote}

# EZ-DOC-5
law plain_lock_pins_ledger_sources:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.pinned.all(W.origins(w), P.packs(w)) == P.packs(w) : List<&2, L.Pack>}
```

`P.packs(w)` is the package list the plan renders, and `pinned.all` resets each package's source to the one the ledger records for its hash, so the second law says every recorded source is the ledger's. Tools are rendered from `M.tools_of` of the ledger with no other input, which holds by unfolding.

Reuses `lock/LAWS.bend origin_first`. Replaces no trail. Effort: small. The walk invariant is proved in the spike (`walk_pins_ledger_sources`, with one lemma per step def); what is left is the step from the walk to `P.packs`, and the first law, which holds because a plain plan has no `Write` to ez.toml.

### EZ-DOC-2: canonical order

```
# EZ-DOC-2
law lock_order_free:
  for +ns: List<&2, Nat>
  for +ps: List<&2, L.Pack>
  for +ts: List<&2, M.Tool>
  for +hub: String
  for dis: {L.distinct(ps) == True{} : Bool}
  {L.render.tools(ts, hub, L.perm(ns, ps)) == L.render.tools(ts, hub, ps) : String}
```

and a second law that a package's files render the same in any order, which is `pkg/LAWS.bend manifest_perm` again, since `pack.sects` renders `K.files_of`.

The proof for files exists. For packages, `pack.sort` is a second insertion sort with the same shape as `file.sort`, and `pkg/PROOF.bend` spends most of its 2189 lines on the permutation argument for `file.sort`. A generic sort by key would share it, but Bend's function values are linear, so a key function applied at every comparison cannot be passed in. Instead we render each package to its own text block and sort the blocks as `K.File{hash, block}` values with `K.file.sort`; then `sort_perm` applies unchanged, and distinct paths is distinct hashes. The walk guarantees distinct hashes (it skips a hash it has), which is one more walk invariant in the style of `walk_pins_ledger_sources`.

Reuses `pkg/LAWS.bend sort_perm`, `manifest_perm`, `distinct`, `perm`. Replaces `lock/LAWS.bend hashes_sorted` (toward EZ-DOC-2). Effort: medium, with the render refactor and the distinctness invariant as the key lemmas.

### EZ-DOC-1: the lock reads back

```
# EZ-DOC-1
law lock_reads_back:
  for +ps: List<&2, L.Pack>
  for +ts: List<&2, M.Tool>
  for +hub: String
  for ok: {P.lockable(ps, ts, hub) == True{} : Bool}
  {L.packs(T.sects(T.parse(L.render.tools(ts, hub, ps)))) == L.canon(ps)
    : List<&2, L.Pack>}
```

with two companions for the hub (`L.lock.hub(...) == hub`) and the tools (`M.tools(...) == ts`). `canon` is `pack.sort` with each package's files through `K.files_of`. `lockable` says every hash is distinct and has no `"`, and no key or value holds `"`, `\` or a newline; the planner refuses a lock that is not lockable, so the premise holds of every lock ez writes.

The proof has seven layers. Values survive trim and strip, and a split at `=` joins back (proved in the spike: `trim_quoted`, `strip_quoted`, `join_split`, with `char_eq_true`, reflecting `Char.is_eq` into equality by induction over the 32-bit word). Keys: a bare key computes, a quoted path is a value. Line classification: a pair line is not blank, not a comment, not a header, and holds `=`. Headers: `segments` of `packages."<h>".files` is three segments, a walk like trim's. Lines: `String.lines` of the rendered text is the concatenation of each section's lines, by the `spec_split` lemma generalized from `/` to any separator. The reader's state machine, over sections. And the ez side: `hashes`, `at3`, `pack_of` and `T.value` find the section and key that were written, which needs distinct hashes and string equality reflected, the latter following from `char_eq_true`.

Reuses `lock/PROOF.bend spec_split`, `check/eq.bend`, and the spike's string lemmas. Replaces `lock/LAWS.bend lock_roundtrip` and `tool_pin_reads_back` (toward EZ-DOC-1). `tools_are_not_packages` points toward EZ-LED-5 and stays. Effort: large, the largest in the phase; we estimate 1500 to 3000 lines of proof. The spike's first layer took about 250 lines and went through with only linearity and ordering fixes, which is why we do not propose moving it to Trusted. Route (a) is decided. If it stalls, the sections-level law alone is a useful stopping point, and moving the text layer to Trusted would be a new decision.

### EZ-DOC-4: idempotence

```
# EZ-DOC-4
law lock_idempotent:
  for +w: W.World
  for ok: {P.refuses(w) == False{} : Bool}
  {P.put(P.after(w), "ez.lock.toml") == P.put(w, "ez.lock.toml") : P.Wrote}

# EZ-DOC-4
law upgrade_settles:
  for +w: W.World
  for ok: {P.refuses(w) == False{} : Bool}
  {P.put(P.after(w), "ez.toml") == P.Kept{} : P.Wrote}
```

`P.after(w)` is the World the plan leaves: its ledger is the written ez.toml, its sources the rewritten ones, each laid tree answers from BEND_LIB with the bytes laid, and every remote answer is what it was, because the remote did not change between the two runs.

For a plain lock this is a corollary of `clone_reproduces` read backwards: the only thing a plain plan changes that the lock reads is which trees are under BEND_LIB. Under `--upgrade` the second run asks each moved pin's remote again, gets the same tip, finds the pin equal to it, confirms the checkout with `U.agree` against the hash, narHash and root the first run wrote, and so keeps it (`U.Keep`), and a ledger with nothing moved is not rewritten.

Reuses `clone_reproduces`, `check/eq.bend string_eq_self`. Replaces `manifest/LAWS.bend same_rev_keeps` (toward EZ-DOC-4). Effort: small for the plain lock, medium to large for the upgrade, whose key lemma is that a dependency's verdict on its own tip is `Keep` with agreement.

**Update:** WP5a has landed the plain half as `lock/LAWS.bend lock_idempotent` and `relock_lays_nothing`. Where it differs from the sketch: `after` is law vocabulary in `lock/LAWS.bend`, not `P.after`, and a refused lock leaves the World it read, so `lock_idempotent` needs no premise. The second law is about BEND_LIB rather than ez.toml, which a plain lock never writes (EZ-DOC-5): after a lock that succeeded, no tree arrives by a clone that passes, so none is laid again. `upgrade_settles` is WP5b's.

### EZ-RES-4, EZ-RES-5, EZ-RES-6, EZ-RES-8: the upgrade's decisions

All four are stated over `P.ledger.next(w)`, the ledger model the plan renders, which is the old ledger when the plan refuses or writes nothing. `W.dep(w, n)` is `M.dep(M.parse(w.ledger), n)`. `P.answered(w)` is `P.wants(w) == []`.

```
# EZ-RES-4
law upgrade_holds_hub:
  for +w: W.World
  for +n: String
  for hub: {M.source.is_git(M.source.dep(W.dep(w, n))) == False{} : Bool}
  {M.dep(P.ledger.next(w), n) == W.dep(w, n) : M.Dep}

# EZ-RES-5
law upgrade_forward_moves_onward:
  for +w: W.World
  for +n: String
  for bare: {P.rev_only(W.dep(w, n)) == True{} : Bool}
  {P.forward.ok(w, n) == True{} : Bool}

# EZ-RES-5
law upgrade_forward_refuses_off:
  for +w: W.World
  for +n: String
  for bare: {P.rev_only(W.dep(w, n)) == True{} : Bool}
  for sel: {U.chosen(W.args.only(w), n) == True{} : Bool}
  for done: {P.answered(w) == True{} : Bool}
  for moved: {String.eq(P.tip(w, n), P.pin(w, n)) == False{} : Bool}
  for off: {P.onward(w, n) == False{} : Bool}
  {P.refuses(w) == True{} : Bool}

# EZ-RES-6
law upgrade_one_frames_others:
  for +w: W.World
  for +n: String
  for +m: String
  for e: {W.args.only(w) == n : String}
  for d: {String.eq(n, m) == False{} : Bool}
  {M.dep(P.ledger.next(w), m) == W.dep(w, m) : M.Dep}

# EZ-RES-6
law upgrade_one_asks_one:
  for +w: W.World
  for +n: String
  for e: {W.args.only(w) == n : String}
  {P.resolves.only(P.wants(w), P.url(w, n)) == True{} : Bool}

# EZ-RES-8
law upgrade_tag_follows:
  for +w: W.World
  for +n: String
  for tag: {P.tagged(W.dep(w, n)) == True{} : Bool}
  {P.follow.ok(w, n) == True{} : Bool}
```

`forward.ok(w, n)` is law vocabulary in LAWS.bend: the plan refuses, or the new pin's rev is the old one, or it is the tip the `Head` answer names and the `Above` answer for the old pin and that tip is yes; and the new pin's tag is empty. `follow.ok` is the same for a tag, with the `Refs` answer in place of `Head`, the tag kept, and refusal required on `Off` and on a same-commit checkout that `U.agree` rejects (drift). There is a matching tool law for each, over `M.tool.find`.

These are pointwise facts about a walk over the ledger's dependencies, so each proof is one lemma about one dependency's verdict (`U.aim`, then `U.judge`, then `U.retarget`) and an induction over the list with `M.find`. EZ-RES-5 and EZ-RES-8 read `Printed` answers through `Git.tip.rev`, `Git.tip.branch` and `Git.exact`; the laws take those parsers as given, and a quantified law about each parser replaces the closed ones in `git/LAWS.bend`.

| Law | Reuses | Replaces | Effort |
| :---- | :---- | :---- | :---- |
| EZ-RES-4 | `U.aim` of a hub source is `Hold` | `manifest/LAWS.bend hub_holds` | small |
| EZ-RES-5 | `U.judge`, `U.retarget`, `Git.tip.*` | `sha256_aims_forward`, `sha256_advances`, `sha256_retarget` (manifest); `sha256_remote_tip`, `sha256_remote_branch` (git), once a quantified `tip.rev` law is in | medium; key lemma: a `Forward` pin's verdict is `Advance` exactly when the tip differs and is onward |
| EZ-RES-6 | `U.chosen`, `U.aim(False, _) == Hold` | `manifest/LAWS.bend unselected_holds` | small for the frame, medium for the asks, whose key lemma is that `wants` only asks resolution questions about a selected entry |
| EZ-RES-8 | `U.judge` with its agreement bit live, `U.agree` | `tag_follows`, `same_rev_drifts`, `tag_moved_off` (manifest) | medium |

**Update:** WP6's second half has landed EZ-RES-5 and EZ-RES-8, proved relative to EZ-LED-4 and EZ-RES-7. Where the laws differ from the sketches above:

- `forward.ok` and `follow.ok` are law vocabulary in `lock/LAWS.bend`, both one `moved.ok(tip, rs, old, new)`: the new pin is still from a repository, has the tag the old one had, and is at the old commit or at the commit `tip` names when the `Above` answer for the old commit and that one is yes. `rev_only` and `tagged` are law vocabulary too, not `P.` defs. "The plan refuses" is not an arm of `moved.ok`: `P.ledger.next` is ez.toml's model whenever the upgrade refuses, so `upgrade_forward_moves_onward` and `upgrade_tag_follows` hold of every World without it.
- The refusal laws (`upgrade_forward_refuses_off`, `upgrade_tag_refuses_off`, and `upgrade_tag_refuses_drift` for a tag that still names the pinned commit whose checkout `U.agree` rejects) take the remote's answers about the one pin as premises, `Up.forward` or `Up.follow` answering `At{tip, ...}` and `Up.onward` answering `Asc{False}`, and need no `P.answered`: a refusal ahead of the rest wins whatever the other pins were answered.
- Two laws the sketch did not have, `upgrade_forward_reaches_tip` and `upgrade_tag_resolves`, say that when the upgrade asks about a pin and the lock does not refuse, the pin in `P.ledger.next` is at the commit the remote named. Without them a planner that never moved a pin would meet every other law here, and EZ-RES-8's "re-resolves its tag" would not be stated.
- `Git.tip.rev`, which reads the default branch tip, has three quantified laws in `git/LAWS.bend` tagged EZ-RES-5 (`tip_of_head`, `tip_skips_other`, `tip_skips_symref`). `Git.tip.branch` and `Git.exact` already had A5's, tagged EZ-RES-1.
- The proofs are in `lock/PROOF.bend` under `mv.`: one fate lemma per def of `Up.dep.tip` for any tip, so a tag and the default branch share them; the walk by induction over the ledger's dependencies, carrying that every fate keeps its dependency's name and waits only with a question; and the model through each way `Up.next` can end. `lock/PROOF.bend` checks in about 13 s before and after.
- The matching tool laws are not written. EZ-RES-5 and EZ-RES-8 are about dependencies; `tool.verdict` calls the same `U.judge`.

Decided while proving: a refusal always has a reason. WP2's upgrade read an empty reason as no refusal, in `pins` and in `Next.stop`, so a dependency or tool whose pin halted with the reason "" dropped out of the ledger the upgrade wrote, and an upgrade that stopped with "" went on to lock ez.toml as it was. Only a `Miss{""}` answer reached either, and the interpreter never builds one, so the binary behaves as before. `Up.halt.why` gives such a refusal a fixed reason in `deps.join`, `tools.join` and `stopped`. We chose that over counting refusals with a separate flag in `pins` because `Next.stop` and `W.Inputs.stop` are text by WP1's and WP2's design, and a flag in `pins` alone would leave the same hole in `stopped`. Cargo and uv also report every failed resolution with a message.

### EZ-VEN-1, EZ-VEN-2, EZ-VEN-3: what the upgrade writes around the ledger

```
# EZ-VEN-1
law upgrade_allowlist_is_the_ledger:
  for +w: W.World
  {I.hashes(P.ignore.lines(w)) == I.vended(P.deps.next(w)) : List<&2, String>}

# EZ-VEN-1
law upgrade_allowlist_keeps_other_lines:
  for +w: W.World
  {I.others(P.ignore.lines(w)) == I.others(P.ignore.lines.before(w)) : List<&2, String>}

# EZ-VEN-2
law upgrade_rewrites_imports:
  for +w: W.World
  for +at: String
  for +i: Nat
  for +s: U.Swap
  for hit: {P.swapped(w, at, i, s) == True{} : Bool}
  {U.reimport.hash(P.line(P.source.next(w, at), i)) == U.Swap.new(s) : String}

# EZ-VEN-3
law upgrade_leaves_other_lines:
  for +w: W.World
  for +at: String
  for +i: Nat
  for miss: {P.swapped.any(w, at, i) == False{} : Bool}
  {P.line(P.source.next(w, at), i) == P.line(P.source.before(w, at), i) : String}

# EZ-VEN-3
law upgrade_writes_only_hits:
  for +w: W.World
  for +at: String
  for none: {P.hits(w, at) == False{} : Bool}
  {P.put(w, at) == P.Kept{} : P.Wrote}
```

`ignore.lines(w)` is the lines of the `.gitignore` the plan leaves (written or not), `source.next(w, at)` the text of source `at` after the plan, and `swapped(w, at, i, s)` says line `i` of the old text named `s.old` at column 0. Only `ez lock --upgrade` is in this phase; `ez add` and `ez remove` meet EZ-VEN-1 when they are converted.

EZ-VEN-1's line-level half is proved (`manifest/LAWS.bend allowlist_is_the_ledger`, `allowlist_keeps_other_lines`). What is left is the text layer of `I.sync`, which is "Left to prove" in `SPEC.md`: that `String.lines` of `String.join(ls, "\n")` is `ls` when no line holds a newline, which is the dual of the spike's `join_split`, and that a file left unwritten is the file `I.sync` would have made, which needs string equality reflected. EZ-VEN-2 and EZ-VEN-3 need the same `lines` after `join` lemma to go from `reimport` to its lines, then a lemma about one rewritten line, then an induction over the swaps with their old and new hashes disjoint, which is the premise the RFC already calls for.

| Law | Reuses | Replaces | Effort |
| :---- | :---- | :---- | :---- |
| EZ-VEN-1 | `allowlist_is_the_ledger`, `allowlist_keeps_other_lines`, the spike's `join_split` | nothing; its laws are already tagged | medium |
| EZ-VEN-2 | the spike's `char_eq_true`, lifted to strings | `manifest/LAWS.bend imports_follow_hash` | medium to large; key lemma: `reimport.hash` of a rewritten line is the new hash |
| EZ-VEN-3 | `join_split` with `\n`, `string_eq_self` | shares `imports_follow_hash` with EZ-VEN-2 | medium |

### EZ-HASH-2: NAR order

```
# EZ-HASH-2
law nar_dir_order_free:
  for +ns: List<&2, Nat>
  for +es: List<&2, K.File>
  for dis: {distinct(es) == True{} : Bool}
  {Nar.dir(perm(ns, es)) == Nar.dir(es) : String}
```

`Nar.dir(es)` is a new pure def: `Nar.directory` of the entries after `K.file.sort`, where each entry is encoded as `K.File{name, serial}`. `sha/nar.bend` today sorts the names `find` printed before loading the children; it would load them in `find`'s order and sort the loaded entries instead, which is the same serialization. With that encoding the proof is `pkg/LAWS.bend sort_perm` applied under `Nar.directory`, and `distinct` is distinct names, which a directory has. Every directory's serial goes through `Nar.dir`, so the law at one level is the requirement.

Reuses `sort_perm`, `perm`, `distinct`. Replaces no trail. Effort: small. It does not depend on the planner and can start at once.

### Trails this phase deletes

`lock/LAWS.bend`: `hashes_sorted`, `lock_roundtrip`, `tool_pin_reads_back`. `manifest/LAWS.bend`: `sha256_aims_forward`, `hub_holds`, `tag_follows`, `unselected_holds`, `sha256_advances`, `same_rev_keeps`, `same_rev_drifts`, `tag_moved_off`, `sha256_retarget`, `imports_follow_hash`. `git/LAWS.bend`: `sha256_remote_tip`, `sha256_remote_branch`. Each goes in the change that lands the law naming it above. The trails toward EZ-LED-4, EZ-LED-5, EZ-VEN-5, EZ-TOOL-* and EZ-FETCH-1 stay.

**Update:** these trails, and every other trail, are already gone. We deleted all 40 remaining `# toward` laws in one change, ahead of the laws that were to replace them, so that ez could move to the bolt whose strict `closed` and `trace` rules check `SPEC.md` (see the RFC's "Retiring closed laws"). Where a WP above says it replaces a closed law, there is nothing left to delete: the WP lands its quantified law and tags it.

## The spike

The spike lives in `lock/world/` and is inside the proof gate. It changes no behavior: nothing imports `lock/world/world.bend`, and `ez lock` still runs `lock/lock.bend`. Its laws carry no requirement tag, because the planner they are about is not the one `ez lock` runs.

What it contains:

- `world.bend` (476 lines): the World, `How`, `Answer`, `Inputs` and `Outcome` for plain `ez lock`; `accept`, which checks a package's manifest against its name, its paths against escaping, each text against its sum, a clone's narHash against the ledger's, and refuses a git package with no files; the walk, as one step iterated under fuel; and `plan`, which returns the lock's text, a refusal, or the hashes it still needs.
- `LAWS.bend` and `PROOF.bend` (97 and 765 lines): seven laws, and 34 lemmas stated and proved in `PROOF.bend`.

| Law | Says | Proof |
| :---- | :---- | :---- |
| `plan_frame` | two Worlds with equal `inputs` plan the same | congruence, since `plan` is `plan.of(inputs(w))` |
| `lib_judged_as_clone` | a BEND_LIB tree is judged as the same bytes cloned and weighed to the ledger's narHash | a case split on the source |
| `clone_reproduces` | a World whose trees came from BEND_LIB plans as the fresh-clone World | induction over the replies, one lemma per kind of answer |
| `walk_pins_ledger_sources` | every package the walk resolves carries the ledger's source for its hash | one lemma per step def, then induction on fuel |
| `trim_quoted` | eztoml's `trim` leaves a quoted value as it is | two passes as list reversals: five list lemmas |
| `strip_quoted` | eztoml's `strip` of a quoted value is the value | a walk to the last char |
| `join_split` | joining a split at a char gives the text back | induction, with `char_eq_true`: `Char.is_eq` reflected into equality through `Word.cmp` |

The evidence:

```
$ BEND_LIB=$PWD/.ez/lib bend lock/world/PROOF.bend
All terms check.
$ BEND_LIB=$PWD/.ez/lib bin/ez.bin prove
...
PASS: 10 / 10
$ bolt.bin --gpu off
0 errors, 363 warnings        (358 before the spike; the new ones are L001, defs no law names)
```

We also ran the planner, outside the gate, on a two-package sample in which the project imports `0xb` and `0xb` imports `0xa`: with no replies it asked for `0xb`; with `0xb` answered it asked for `0xa`; with both answered it returned the lock, both packages in hash order; and with one file's text changed by a byte it refused.

What the spike tells us. The World and the planner are total pure terms with no `unsafe` def; the checker needed no fuel tricks beyond the walk's own. EZ-DOC-3 and the walk half of EZ-DOC-5 are small once the planner is shaped for them. The string layer of EZ-DOC-1, which we expected to be the hardest part of the phase, went through at about the rate `lock/PROOF.bend` and `manifest/PROOF.bend` were written: every failure was linearity (`+` on a binder used twice), definition order, or a def that matched on a value it had not been given as a parameter, and each was fixed in one edit.

What it does not tell us. It has no upgrade, no interpreter, and no performance measurement. The upgrade laws are pointwise over dependencies and look like the walk invariant it did prove, but they read `Printed` answers through git's parsers, which the spike did not exercise. The re-verification cost of the demand loop is an estimate from the round count, not a measurement.

## Work packages

|  |
|:---:|
| <pre>  WP0 lemmas ------------------------------+------------------+<br>                                           |                  |<br>  WP1 plain planner --+--> WP2 upgrade --+--+--> WP6 RES      +--> WP7 VEN<br>         |            |                  |<br>         |            +--> WP5b DOC-4 (upgrade)<br>         +--> WP3 DOC-2 --> WP4 DOC-1<br>         +--> WP5a DOC-4 (plain), DOC-3, DOC-5<br><br>  WP8 HASH-2 (independent)</pre> |
| Caption: An arrow means "starts after". WP0, WP1 and WP8 can start at once. |

| WP | Scope | Needs | Effort |
| :---- | :---- | :---- | :---- |
| WP0 | Move the spike's string lemmas into a shared `check/str.bend`: list reversal, `to_list` and `from_list`, `join_split`, `char_eq_true`, and add `string_eq_true` and `split_join` for pieces without the separator. No behavior change. | nothing | small |
| WP1 | Plain `ez lock` in planner form: `lock/world.bend`, `lock/plan.bend`, `lock/run.bend` seeded from the spike; `wants` and `plan`; `lockable`; delete the IO half of `lock/lock.bend` and the spike. The behavior changes decided above. Lands EZ-DOC-3 and EZ-DOC-5 (tagged), and EZ-OUT-2's law for a plain lock (untagged until WP2 covers `--upgrade`). | nothing | medium |
| WP2 | `ez lock --upgrade` in the same planner: the upgrade questions, `lock/up.bend` from `ez/upgrade.bend` and `ez/pin.bend`, one ez.toml write, effects in the stated order; delete `Up.run`, `Pin.upgrade` and their IO. Lands EZ-OUT-2 for `ez lock` (tagged). | WP1 | large |
| WP3 | EZ-DOC-2: render packages as sorted `K.File` blocks, the distinct-hash walk invariant, the law. | WP1 | medium |
| WP4 | EZ-DOC-1, sections first, then text. | WP0, WP3 (the render it reads back) | large |
| WP5a | EZ-DOC-4 for a plain lock, as a corollary of `clone_reproduces`. | WP1 | small |
| WP5b | EZ-DOC-4 for `--upgrade`: `after`, and a pin at its own tip is kept. | WP2 | medium to large |
| WP6 | EZ-RES-4, 5, 6, 8, and quantified laws for `Git.tip.*` and `Git.exact`. | WP0, WP2 | medium each; they can run as two agents (4 and 6, then 5 and 8) |
| WP7 | EZ-VEN-1 text layer, EZ-VEN-2, EZ-VEN-3. | WP0, WP2 | medium to large |
| WP8 | EZ-HASH-2: pure `Nar.dir`, `sha/nar.bend` sorting loaded entries, the law. | nothing | small |

Each WP ends with the gate passing, bolt at zero errors (`trace` included), its laws tagged, and `SPEC.md` and the inventory updated for the requirements it proved. WP1 and WP2 are the only ones that change behavior, and each lists its changes in its PR description.

## Risks

**The demand loop is slower than today's walk.** A plain lock re-runs `wants` once per level of the import graph. `wants` only scans, and `plan` verifies once, so the added cost is scanning; we will measure it on this repository's own lock in WP1 before WP2 builds on it.

**A World that answers what the interpreter did not ask.** Laws quantify over every World, including ones no interpreter would build, such as one where a hub package is answered as a clone. The planner refuses those (`hub.how` in the spike), so the laws stay true of them; what the laws cannot say is that the interpreter builds only sensible Worlds, which is EZ-TRUST-2.

**EZ-DOC-1 is large.** The spike removed the part we were least sure of, but the remaining layers are many. If it stalls, the sections-level law is a useful stopping point on its own.

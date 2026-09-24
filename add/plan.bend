# add/plan: `ez add` as a pure planner. It reads a World (add/world.bend) and
# returns either the questions it still needs answered (`step`) or a Plan:
# the effects to run and how the command ends (`plan`). The interpreter
# (add/run.bend) loops on `step`, answering each question by IO, until
# nothing is left to ask, then executes the plan.
#
# Before it asks anything the planner refuses what needs no answer: no
# ledger, one that does not parse, a target that names nothing, a `--rename`
# that is no TOML bare key, and a name clash the ledger alone decides (a
# `--rename`, or a source it already records). Then it asks at most three
# rounds: what the ref names (the remote's tags, then its HEAD when no tag is
# semver-ish; or the named ref), then the checkout at that rev, which carries
# its NAR hash and the text of every file. A 40-hex ref is the commit, and
# the first question is the checkout. Every question carries the source as
# git is to read it, `P.anchor(here, url)`, which the planner computes.
#
# With the checkout answered, the package is walked from its entry by the
# pure walk (`K.of`) over the checkout's files, so the hash, the texts laid
# and the manifest come from one list. The entry is the one given, else the
# checkout's `[package] entry`, `bin` or `main.bend`, and one the checkout
# does not hold is refused. The name is `Named.as`'s, refused when
# `Named.why.as` objects.
#
# The plan of an add that succeeds, in order: the tree laid under
# `$BEND_LIB`, or under `.ez/lib` when the entry it replaces is vendored;
# ez.toml written with the dependency added (`Rend.add.keep`, which keeps
# that vendor bit); `.gitignore` written when the allowlist `I.sync` derives
# from the new ledger changes it; the old committed tree removed when a
# vendored dependency's hash moved and nothing else names it; and the lines a
# person is told. A refusal has no effect at all: nothing laid, nothing
# written, no cache fill.
#
# A target bend reads as a hub package's `<name>@<version>` is planned by
# add/hub.bend instead (`H.plan`). `command` is the plan `ez add` runs, which
# is `plan` for a git or path target and `H.plan` for a name, and `next` is
# the interpreter's step over both.
#
# The Effect, Plan and Outcome types are the lock's (lock/plan.bend), as for
# `ez remove` and `ez init`; see "Update (A1, A4)" and "Update (A2)" in
# docs/rfc/ez-add-planner.md.
import Base
import ./world.bend as A
import ./hub.bend as H
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/up.bend as Up
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/ignore.bend as I
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
import ../git/git.bend as Git
import ../ez/named.bend as Named
import ../ez/target.bend as Tgt

# ---------------------------------------------------------------------------
# the questions

# a question, before it is told which source it is about: the remote's tags,
# its HEAD, what a named ref names, or the checkout at a rev
type Q is Data:
  QTags{}
  QHead{}
  QRefs{ref: String}
  QClone{rev: String}

# a question about a source
def ask.of(question: Q, +from: String) -> Up.Ask:
  match question:
    case QTags{}:
      Up.Tags{from}
    case QHead{}:
      Up.Head{from}
    case QRefs{ref}:
      Up.Refs{from, ref}
    case QClone{rev}:
      Up.Clone{from, rev}

# each question about a source
def asks.of(qs: List<&2, Q>, +from: String) -> List<&2, Up.Ask>:
  match qs:
    case []:
      []
    case h <> t:
      ask.of(h, from) <> asks.of(t, from)

# what git printed for a question about the World's source
def said(+world: A.World, question: Q) -> Up.Said:
  Up.printed(A.replies(world), ask.of(question, A.from(world)), "ls-remote " ++ A.url(world))

# what was printed, "" when nothing was
def said.text(printed: Up.Said) -> String:
  match printed:
    case Up.Said{text}:
      text
    case Up.Unsaid{_why}:
      ""
    case Up.Unasked{_ask}:
      ""

# the rows git printed for a question, none when nothing was
def rows(+world: A.World, question: Q) -> List<&2, Git.Row>:
  Git.rows(String.lines(said.text(said(world, question))))

# ---------------------------------------------------------------------------
# what the ref names

# the ref `ez add` pins when none was asked for: the tag `Git.choose` takes
# from every tag on the remote, the greatest release, else the greatest
# pre-release; else the branch HEAD's symref names (EZ-RES-1)
def default.ref(+world: A.World) -> String:
  +chosen = Git.choose(Git.tag.names(rows(world, QTags{})))
  Bool.pick(String, String.is_empty(chosen), Git.tip.branch(rows(world, QHead{})), chosen)

# the tag or branch recorded, as a ref was given: none for a commit, the
# default one for none, and the ref itself otherwise
def tag.of(rev: Bool, empty: Bool, +world: A.World) -> String:
  match rev:
    case True{}:
      ""
    case False{}:
      Bool.pick(String, empty, default.ref(world), A.ref(world))

# the tag or branch the ledger records
def tag(+world: A.World) -> String:
  tag.of(Git.is_rev(A.ref(world)), String.is_empty(A.ref(world)), world)

# the commit a ref names, a question still to ask, or why there is none
type Tip is Data:
  At{rev: String}
  TipAsk{q: Q}
  TipNo{why: String}

# a commit the rows named, or why they named none
def tip.found(+rev: String, why: String) -> Tip:
  Bool.pick(Tip, String.is_empty(rev), TipNo{why}, At{rev})

# a named ref, read exactly as `refs/tags/<ref>`, its peeled commit first,
# then `refs/heads/<ref>`
def tip.refs(printed: Up.Said, +world: A.World) -> Tip:
  match printed:
    case Up.Said{text}:
      tip.found(Git.exact(Git.rows(String.lines(text)), A.ref(world)),
        "ez: " ++ A.url(world) ++ " has no ref named " ++ A.ref(world))
    case Up.Unsaid{why}:
      TipNo{why}
    case Up.Unasked{_ask}:
      TipAsk{QRefs{A.ref(world)}}

# the default branch, when no tag is semver-ish: the commit HEAD names, and
# the branch its symref names, which is recorded as the ref followed
def tip.head.rows(+rows: List<&2, Git.Row>, +world: A.World) -> Tip:
  Bool.pick(Tip, String.is_empty(Git.tip.branch(rows)),
    TipNo{"ez: " ++ A.url(world) ++
      " has no semver-ish tag and its HEAD names no branch; name a ref to pin"},
    tip.found(Git.tip.rev(rows), "ez: " ++ A.url(world) ++ " has no HEAD"))

def tip.head(printed: Up.Said, +world: A.World) -> Tip:
  match printed:
    case Up.Said{text}:
      tip.head.rows(Git.rows(String.lines(text)), world)
    case Up.Unsaid{why}:
      TipNo{why}
    case Up.Unasked{_ask}:
      TipAsk{QHead{}}

# the tag chosen, through its peeled commit, or HEAD when none was
def tip.chosen(none: Bool, +chosen: String, +rows: List<&2, Git.Row>, +world: A.World) -> Tip:
  match none:
    case False{}:
      tip.found(Git.exact(rows, chosen),
        "ez: " ++ A.url(world) ++ " has no tag named " ++ chosen)
    case True{}:
      tip.head(said(world, QHead{}), world)

def tip.tags.rows(+rows: List<&2, Git.Row>, +world: A.World) -> Tip:
  +chosen = Git.choose(Git.tag.names(rows))
  tip.chosen(String.is_empty(chosen), chosen, rows, world)

def tip.tags(printed: Up.Said, +world: A.World) -> Tip:
  match printed:
    case Up.Said{text}:
      tip.tags.rows(Git.rows(String.lines(text)), world)
    case Up.Unsaid{why}:
      TipNo{why}
    case Up.Unasked{_ask}:
      TipAsk{QTags{}}

# a ref that is not a commit: the default one, or the one named
def tip.named(empty: Bool, +world: A.World) -> Tip:
  match empty:
    case True{}:
      tip.tags(said(world, QTags{}), world)
    case False{}:
      tip.refs(said(world, QRefs{A.ref(world)}), world)

# a 40-hex ref is the commit, and asks the remote nothing
def tip.of(rev: Bool, empty: Bool, +world: A.World) -> Tip:
  match rev:
    case True{}:
      At{A.ref(world)}
    case False{}:
      tip.named(empty, world)

# the commit the ref names
def tip(+world: A.World) -> Tip:
  tip.of(Git.is_rev(A.ref(world)), String.is_empty(A.ref(world)), world)

def tip.rev(tip: Tip) -> String:
  match tip:
    case At{rev}:
      rev
    case TipAsk{_q}:
      ""
    case TipNo{_why}:
      ""

# the commit pinned, "" while it is not known
def rev(+world: A.World) -> String:
  tip.rev(tip(world))

# ---------------------------------------------------------------------------
# the checkout

# the checkout at the rev: its NAR hash and every file's text, or the
# question still open, or why there is none
type Co is Data:
  Co{nar: String, files: List<&2, K.Source>}
  CoWait{}
  CoNo{why: String}

def co.of(answer: Up.Answer) -> Co:
  match answer:
    case Up.Cloned{nar, fs}:
      Co{nar, fs}
    case Up.Miss{why}:
      CoNo{why}
    case _:
      CoNo{"ez: a checkout was not answered with one"}

def co.heard(got: Up.Heard) -> Co:
  match got:
    case Up.Open{}:
      CoWait{}
    case Up.Heard{answer}:
      co.of(answer)

# the checkout at a rev, as the World answered it
def co.at(+world: A.World, +rev: String) -> Co:
  co.heard(Up.heard(A.replies(world), ask.of(QClone{rev}, A.from(world))))

# the checkout at the rev the ref names
def co(+world: A.World) -> Co:
  co.at(world, rev(world))

def co.files(checkout: Co) -> List<&2, K.Source>:
  match checkout:
    case Co{_nar, fs}:
      fs
    case CoWait{}:
      []
    case CoNo{_why}:
      []

def co.nar(checkout: Co) -> String:
  match checkout:
    case Co{nar, _fs}:
      nar
    case CoWait{}:
      ""
    case CoNo{_why}:
      ""

# every file of the checkout, none while it is not known
def files(+world: A.World) -> List<&2, K.Source>:
  co.files(co(world))

# the checkout's NAR hash
def nar(+world: A.World) -> String:
  co.nar(co(world))

# the checkout's own ez.toml, None when it has none
def tree.toml(+world: A.World) -> Maybe<&2, String>:
  K.look(files(world), "ez.toml")

# the `[package] name` the checkout gives itself, "" for none
def pkg(+world: A.World) -> String:
  Git.called.maybe(tree.toml(world))

# the entry the package is walked from: the one given, else the checkout's
# `[package] entry`, else its `bin`, else `main.bend` (EZ-RES-2)
def entry(+world: A.World) -> String:
  Bool.pick(String, String.is_empty(A.entry.arg(world)),
    Git.entry.maybe(tree.toml(world)), A.entry.arg(world))

# fuel enough for a walk over these files: one step for the entry and one for
# every import it can queue, and every import is a line of some file. So a
# walk over a checkout never runs out, and the fuel is a function of the
# checkout rather than a number, which keeps the walk from unrolling when a
# proof reasons about a checkout it does not know.
def fuel(fs: List<&2, K.Source>) -> Nat:
  match fs:
    case []:
      1n
    case K.Source{_at, text} <> t:
      (List.length(&2, String, String.lines(text)) + fuel(t) : Nat)

# the package the entry is published as, walked over the checkout's files
def walked(+world: A.World) -> K.Walked:
  K.of.fuel(fuel(files(world)), Path.norm(entry(world)), files(world))

# the name the dependency is recorded under (EZ-LED-7)
def name(+world: A.World) -> String:
  Named.as(A.deps(world), A.url(world), A.rename(world), pkg(world), A.fresh(world))

# why that name cannot be recorded, "" when it can
def why(+world: A.World) -> String:
  Named.why.as(A.deps(world), name(world), A.url(world), A.rename(world))

# ---------------------------------------------------------------------------
# what is decided before the walk

# whether the ledger alone decides the name: a `--rename` was given, or the
# ledger already records this source
def decided(+world: A.World) -> Bool:
  Bool.or(Bool.not(String.is_empty(A.rename(world))),
    Bool.not(String.is_empty(Named.had(A.deps(world), A.url(world), ""))))

# why the name is refused before anything is asked, "" when it is not. A
# `--rename` that is no key is always refused here, and a clash only when
# the ledger alone decides the name; one that turns on the checkout's
# `[package] name` is decided after the walk.
def early(+world: A.World) -> String:
  Bool.pick(String, decided(world),
    Named.why.as(A.deps(world),
      Named.as(A.deps(world), A.url(world), A.rename(world), "", A.fresh(world)),
      A.url(world), A.rename(world)),
    "")

# where the World stands before the walk: every answer it needs is in, a
# question is still open, or the add refuses
type Verdict is Data:
  Go{}
  Wait{qs: List<&2, Q>}
  Stop{why: String}

# the checkout answered, still to ask, or not to be had
def decide.co(checkout: Co, +rev: String) -> Verdict:
  match checkout:
    case Co{_nar, _fs}:
      Go{}
    case CoWait{}:
      Wait{[QClone{rev}]}
    case CoNo{why}:
      Stop{why}

# what the ref names, then the checkout at it
def decide.tip(tip: Tip, +world: A.World) -> Verdict:
  match tip:
    case At{+rev}:
      decide.co(co.at(world, rev), rev)
    case TipAsk{q}:
      Wait{[q]}
    case TipNo{why}:
      Stop{why}

# a name refused before anything is asked
def decide.early(ok: Bool, +why: String, +world: A.World) -> Verdict:
  match ok:
    case True{}:
      decide.tip(tip(world), world)
    case False{}:
      Stop{why}

# a target that names nothing is refused before anything is asked
def decide.place(place: Tgt.Place, +world: A.World) -> Verdict:
  match place:
    case Tgt.Bad{why}:
      Stop{"ez: " ++ why}
    case Tgt.Local{_path}:
      +e = early(world)
      decide.early(String.is_empty(e), e, world)
    case Tgt.Remote{_url, _slug}:
      +e = early(world)
      decide.early(String.is_empty(e), e, world)

# no ledger, or one that does not parse, is refused before anything else,
# with the reason every command that edits a ledger gives
def decide.read(read: M.Read, +world: A.World) -> Verdict:
  match read:
    case M.Bad{why}:
      Stop{"ez: " ++ M.show(M.Bad{why})}
    case M.Good{_m}:
      decide.place(A.place(world), world)

# where a World stands before the walk
def decide(+world: A.World) -> Verdict:
  decide.read(A.read(world), world)

# ---------------------------------------------------------------------------
# the walk and the name

# the dependency recorded, from the walk's hash and root
def dep.of(+hash: String, +root: String, +world: A.World) -> M.Dep:
  M.Dep{name(world), hash, entry(world),
    M.Git{A.url(world), rev(world), tag(world), root, nar(world), False{}}}

# the ledger with the package added, once it is known to read back. A
# ledger that could not be written so that it reads back, such as one whose
# source or entry holds a quote, is refused (EZ-LED-4).
def outcome.fit(fit: Bool) -> P.Outcome:
  match fit:
    case True{}:
      P.Success{}
    case False{}:
      P.Refused{Rend.unrenderable()}

# the name, once the walk made a package, then the ledger it leaves
def outcome.name(ok: Bool, fit: Bool, +world: A.World) -> P.Outcome:
  match ok:
    case True{}:
      outcome.fit(fit)
    case False{}:
      P.Refused{why(world)}

# the walk's verdict: a package, or why there is none
def outcome.walk(walk: K.Walked, +world: A.World) -> P.Outcome:
  match walk:
    case K.Walked{+h, +root, _fs, _ss}:
      outcome.name(String.is_empty(why(world)),
        Rend.renderable(Rend.add.keep(A.manifest.of(A.read(world)), dep.of(h, root, world))), world)
    case K.Asks{at}:
      P.Refused{"ez: " ++ at ++ " was never read"}
    case K.Refused{why}:
      P.Refused{why}

# the entry has to be in the checkout for there to be a package to walk
def outcome.entry(got: Maybe<&2, String>, walk: K.Walked, +world: A.World) -> P.Outcome:
  match got:
    case None{}:
      P.Refused{"ez: " ++ entry(world) ++ " is not in " ++ A.url(world) ++ " at " ++
        rev(world)}
    case Some{_text}:
      outcome.walk(walk, world)

# how an add over an answered World ends, given its walk
def outcome.k(walk: K.Walked, +world: A.World) -> P.Outcome:
  outcome.entry(K.look(files(world), Path.norm(entry(world))), walk, world)

# ---------------------------------------------------------------------------
# the effects

# the dependency the plan records: the one `dep.of` makes from the walk, or
# an empty one when the walk made none, which no plan writes
def added.k(walk: K.Walked, +world: A.World) -> M.Dep:
  match walk:
    case K.Walked{h, root, _fs, _ss}:
      dep.of(h, root, world)
    case K.Asks{_at}:
      M.Dep{"", "", "", M.Hub{""}}
    case K.Refused{_why}:
      M.Dep{"", "", "", M.Hub{""}}

# the dependency `ez add` records on a World
def added(+world: A.World) -> M.Dep:
  added.k(walked(world), world)

# the ledger `ez add` leaves on a World
def ledger.next(+world: A.World) -> M.Manifest:
  Rend.add.keep(A.manifest.of(A.read(world)), added(world))

# a found file as it is laid
def src.of(item: K.Source) -> W.Source:
  K.Source{at, text} = item
  W.Source{at, text}

# every found file as it is laid
def srcs(fs: List<&2, K.Source>) -> List<&2, W.Source>:
  match fs:
    case []:
      []
    case h <> t:
      src.of(h) <> srcs(t)

# where the tree is laid: under `.ez/lib`, committed, when the entry it
# replaces is vendored, since the re-added entry keeps that bit; under
# BEND_LIB otherwise
def place.of(vend: Bool) -> P.Place:
  match vend:
    case True{}:
      P.Committed{}
    case False{}:
      P.Cache{}

# the rest of a scan only when this step was not the hit
def any.step(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a dependency names this hash
def holds(ds: List<&2, M.Dep>, +hash: String) -> Bool:
  match ds:
    case []:
      False{}
    case +h <> t:
      any.step(String.eq(M.dep.hash(h), hash), _u => holds(t, hash))

# whether a char may stand in a hash that names a directory under `.ez/lib`
def char.ok(+ch: Char) -> Bool:
  Bool.not(Bool.or(Char.is_eq(ch, '/'), Char.is_eq(ch, '\\')))

def chars.ok(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      +rest = chars.ok(t)
      Bool.and(char.ok(h), rest)

# a hash `rm -rf .ez/lib/<hash>` removes one tree for, as `ez remove` checks
# it: a `0x` name with no path separator in it
def safe(+hash: String) -> Bool:
  Bool.and(String.starts_with(hash, "0x"), chars.ok(hash))

# the committed tree a re-add moves off: the old hash of a vendored entry
# when the hash moved, it is safe to remove, and nothing left names it
def gone(+old: M.Dep, +hash: String, +left: List<&2, M.Dep>) -> List<&2, String>:
  Bool.pick(List<&2, String>,
    Bool.and(M.source.vendor(M.source.dep(old)),
      Bool.and(Bool.not(String.eq(M.dep.hash(old), hash)),
        Bool.and(safe(M.dep.hash(old)), Bool.not(holds(left, M.dep.hash(old)))))),
    [M.dep.hash(old)], [])

# `.gitignore` written ahead of the rest when the allowlist changes it
def ignore.put(same: Bool, +next: String, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match same:
    case True{}:
      rest
    case False{}:
      P.Write{A.ignore.file(), next} <> rest

# the entry's path inside a package rooted at `root`, which is where the hub
# serves it: its name alone, unless an import climbs out of its directory and
# re-roots the package above it
def at.of(+root: String, +world: A.World) -> String:
  K.inside(root, Path.norm(entry(world)))

# the lines a person is told: the commit a tag or branch turned out to be,
# and the import line the package is now reachable by, for the entry at `at`
# inside it. `Git.import.line` is the line `ez publish` prints too.
def says(+hash: String, +at: String, +world: A.World) -> List<&2, P.Effect>:
  +line = Git.import.line(hash, at)
  Bool.pick(List<&2, P.Effect>, String.is_empty(tag(world)), [P.Say{line}],
    [P.Say{tag(world) ++ " is " ++ rev(world)}, P.Say{line}])

# what an add that walked a package does: the tree laid, ez.toml written,
# `.gitignore` when the allowlist changes, the old committed tree removed, and
# what a person is told
def effects.of(
  +dep: M.Dep,
  +hash: String,
  +at: String,
  fs: List<&2, K.Source>,
  ss: List<&2, K.File>,
  +manifest: M.Manifest,
  +world: A.World
) -> List<&2, P.Effect>:
  +old = M.find(A.deps.of(manifest), M.dep.name(dep))
  +left = A.deps.of(Rend.add.keep(manifest, dep))
  +next = I.sync(left, A.ignore(world))
  P.Lay{place.of(M.source.vendor(M.source.dep(old))), hash,
    List.append(&2, W.Source, srcs(fs), [W.Source{"manifest", K.manifest_of(ss)}])} <>
    (P.Write{A.toml(), Rend.show(Rend.add.keep(manifest, dep))} <>
      ignore.put(String.eq(next, A.ignore(world)), next,
        P.drops.of(gone(old, hash, left), says(hash, at, world))))

# the effects of an add whose walk made a package; none otherwise
def effects.k(walk: K.Walked, +world: A.World) -> List<&2, P.Effect>:
  match walk:
    case K.Walked{+h, +root, fs, ss}:
      effects.of(dep.of(h, root, world), h, at.of(root, world), fs, ss,
        A.manifest.of(A.read(world)), world)
    case K.Asks{_at}:
      []
    case K.Refused{_why}:
      []

# ---------------------------------------------------------------------------
# the plan

# a plan that refuses has no effect at all; its reason is how it ends
def seal(es: List<&2, P.Effect>, outcome: P.Outcome) -> P.Plan:
  match outcome:
    case P.Success{}:
      P.Plan{es, P.Success{}}
    case P.Refused{why}:
      P.Plan{[], P.Refused{why}}

# the plan once every answer is in, with `k` the walk. The walk is made once
# and read by both halves.
def made(+walk: K.Walked, +world: A.World) -> P.Plan:
  seal(effects.k(walk, world), outcome.k(walk, world))

# the plan for where the World stands. One that still asks is a World the
# interpreter did not finish, and is refused rather than guessed at.
def plan.v(verdict: Verdict, +world: A.World) -> P.Plan:
  match verdict:
    case Go{}:
      made(walked(world), world)
    case Wait{_qs}:
      P.Plan{[], P.Refused{"ez: the remote was never asked what " ++ A.url(world) ++
        " holds"}}
    case Stop{why}:
      P.Plan{[], P.Refused{why}}

# `ez add` over a World
def plan(+world: A.World) -> P.Plan:
  plan.v(decide(world), world)

# whether a plan ends in a refusal
def refuses.plan(pl: P.Plan) -> Bool:
  P.Plan{_es, outcome} = pl
  match outcome:
    case P.Success{}:
      False{}
    case P.Refused{_why}:
      True{}

# whether `ez add` refuses on a World
def refuses(+world: A.World) -> Bool:
  refuses.plan(plan(world))

# the questions still open where the World stands
def qs.v(verdict: Verdict) -> List<&2, Q>:
  match verdict:
    case Go{}:
      []
    case Wait{qs}:
      qs
    case Stop{_why}:
      []

# the questions a World still leaves open, each about the anchored source
def wants(+world: A.World) -> List<&2, Up.Ask>:
  asks.of(qs.v(decide(world)), A.from(world))

# whether every answer the planner needs is in
def answered(+world: A.World) -> Bool:
  List.is_empty(&2, Up.Ask, wants(world))

# the questions still open, or the plan once there are none
type Step is Data:
  Asking{asks: List<&2, Up.Ask>}
  Run{plan: P.Plan}

def step.v(verdict: Verdict, +world: A.World) -> Step:
  match verdict:
    case Go{}:
      Run{plan.v(Go{}, world)}
    case Wait{qs}:
      Asking{asks.of(qs, A.from(world))}
    case Stop{why}:
      Run{plan.v(Stop{why}, world)}

# what the interpreter does next on a World
def step(+world: A.World) -> Step:
  step.v(decide(world), world)

# ---------------------------------------------------------------------------
# law vocabulary

# whether a question asks the remote to resolve a ref: its tags, its HEAD,
# or a named ref. A checkout at a known commit is not resolving.
def resolves.one(ask: Up.Ask) -> Bool:
  match ask:
    case Up.Tags{_url}:
      True{}
    case Up.Head{_url}:
      True{}
    case Up.Refs{_url, _ref}:
      True{}
    case _:
      False{}

# whether any question does
def resolves(as: List<&2, Up.Ask>) -> Bool:
  match as:
    case []:
      False{}
    case h <> t:
      +rest = resolves(t)
      Bool.or(resolves.one(h), rest)

# the source a git question names, "" for any other question
def ask.url(ask: Up.Ask) -> String:
  match ask:
    case Up.Tags{url}:
      url
    case Up.Head{url}:
      url
    case Up.Refs{url, _ref}:
      url
    case Up.Clone{url, _rev}:
      url
    case _:
      ""

# whether every question names this source
def asks.from(as: List<&2, Up.Ask>, +from: String) -> Bool:
  match as:
    case []:
      True{}
    case h <> t:
      +rest = asks.from(t, from)
      Bool.and(String.eq(ask.url(h), from), rest)

# what a path holds once a plan has run, when it held `was` before
def after(wrote: P.Wrote, +was: String) -> String:
  match wrote:
    case P.Kept{}:
      was
    case P.Put{text}:
      text

# the hash of the package the walk made, "" when it made none
def hash.of(walk: K.Walked) -> String:
  match walk:
    case K.Walked{h, _root, _fs, _ss}:
      h
    case K.Asks{_at}:
      ""
    case K.Refused{_why}:
      ""

# the directory its paths are written from, "." when it made none
def root.of(walk: K.Walked) -> String:
  match walk:
    case K.Walked{_h, root, _fs, _ss}:
      root
    case K.Asks{_at}:
      "."
    case K.Refused{_why}:
      "."

# the package's hash on a World
def hash(+world: A.World) -> String:
  hash.of(walked(world))

# the entry's path inside the package on a World, which is where the hub
# serves it
def at(+world: A.World) -> String:
  at.of(root.of(walked(world)), world)

# the last of some lines, `prev` when there are none after it
def last.go(ls: List<&2, String>, +prev: String) -> String:
  match ls:
    case []:
      prev
    case h <> t:
      last.go(t, h)

# the last line a plan says, "" when it says none
def last(pl: P.Plan) -> String:
  last.go(P.said(pl), "")

# ---------------------------------------------------------------------------
# the command: a git or path target, or a hub package's name

# the plan `ez add` runs, once it is known whether the target is a name
def command.of(named: Bool, +world: A.World) -> P.Plan:
  match named:
    case True{}:
      H.plan(world)
    case False{}:
      plan(world)

# the plan `ez add` runs on a World
def command(+world: A.World) -> P.Plan:
  command.of(A.named(world), world)

# whether `ez add` refuses on a World
def refuses.command(+world: A.World) -> Bool:
  refuses.plan(command(world))

# what the interpreter does next: answer git's questions, answer the hub's,
# or run the plan
type Next is Data:
  AskGit{asks: List<&2, Up.Ask>}
  AskHub{asks: List<&2, W.Ask>}
  Done{plan: P.Plan}

# the git planner's step
def next.git(st: Step) -> Next:
  match st:
    case Asking{asks}:
      AskGit{asks}
    case Run{pl}:
      Done{pl}

# the hub planner's step: its questions, or its plan once there are none
def next.hub(asks: List<&2, W.Ask>, +world: A.World) -> Next:
  match asks:
    case []:
      Done{H.plan(world)}
    case h <> t:
      AskHub{h <> t}

def next.of(named: Bool, +world: A.World) -> Next:
  match named:
    case True{}:
      next.hub(H.wants(world), world)
    case False{}:
      next.git(step(world))

# what the interpreter does next on a World
def next(+world: A.World) -> Next:
  next.of(A.named(world), world)

# whether a step still asks anything
def next.asks(nx: Next) -> Bool:
  match nx:
    case AskGit{_asks}:
      True{}
    case AskHub{_asks}:
      True{}
    case Done{_pl}:
      False{}

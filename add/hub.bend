# add/hub: `ez add <name>@<version>` as a pure planner, for a target bend
# reads as a hub package's name (`Tgt.aim`). It reads the same World as the
# git planner (add/world.bend), and asks the lock's own questions of the hub
# the ledger names (lock/world.bend): what the name names (`W.Name`), then
# that package's manifest and files (`W.Pkg`). Their answers are the World's
# `hubs`.
#
# Before it asks anything the planner refuses what needs no answer: no
# ledger, one that does not parse, a ref and an entry both given (a name pins
# its version, so the word after it is the entry), and a key the ledger
# alone refuses (`Named.hub.why`). Then it asks at most two rounds: the name,
# then the package it names. The hub's answer must be a `0x` name, and the
# package is judged as `ez lock` judges a hub package (`W.hub.how`): its
# manifest hashes to that name, no path leaves it, each file hashes to its
# sum, and the files hash to the name (EZ-HASH-3).
#
# With the package in hand, the entry is the one given, which the package
# must hold, else its `main.bend`, else its first top-level `.bend` file in
# manifest order, else none. The key is `Named.hub.key`'s: `--rename`, else
# the key the ledger gives this name part, else the name part itself. The
# plan of an add that succeeds, in order: the tree laid under `$BEND_LIB`;
# the name's file, `$BEND_LIB/names/<name>@<version>`, so bend reads the name
# without asking the hub; ez.toml written with `[deps.<key>]` holding `hub`
# and `hash`; `.gitignore` when the allowlist changes; and the lines a person
# is told, the hash the name names and, when there is an entry, the import
# line. A refusal has no effect at all. `ez add` writes no lock, for a name
# as for a git package: the next `ez lock` reads the name from ez.toml and
# asks the hub nothing (EZ-HUB-2).
import Base
import ./world.bend as A
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/lock.bend as L
import ../manifest/manifest.bend as M
import ../manifest/render.bend as Rend
import ../manifest/ignore.bend as I
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
import ../git/git.bend as Git
import ../ez/named.bend as Named

# ---------------------------------------------------------------------------
# what the World says

# the `<name>@<version>` asked for
def nv(world: A.World) -> String:
  A.target(world)

# its name part, which a re-add of another version finds its entry by
def part(+world: A.World) -> String:
  Named.hub.part(nv(world))

# the key the dependency is recorded under (EZ-LED-7)
def key(+world: A.World) -> String:
  Named.hub.key(A.deps(world), part(world), A.rename(world))

# the entry asked for: the word after the name. A name pins its version, so
# that word is the entry, whichever place it was given in.
def asked(+world: A.World) -> String:
  Bool.pick(String, String.is_empty(A.entry.arg(world)), A.ref(world), A.entry.arg(world))

# this reply's answer when it is about the key, else the rest's. The rest
# arrives as a thunk, so the first answer ends the scan.
def heard.at(hit: Bool, answer: W.Answer, rest: Unit -> Maybe<&2, W.Answer>) -> Maybe<&2, W.Answer>:
  match hit:
    case True{}:
      Some{answer}
    case False{}:
      rest(Unit{})

# the answer the World holds for a question about this key: a name, or a
# package's hash
def heard(rs: List<&2, W.Reply>, +key: String) -> Maybe<&2, W.Answer>:
  match rs:
    case []:
      None{}
    case W.Reply{ask, answer} <> t:
      heard.at(String.eq(W.ask.hash(ask), key), answer, _u => heard(t, key))

# ---------------------------------------------------------------------------
# where the World stands

# every answer is in, with the hash the hub named and the package it serves
# checked against it; a question is still open; or the add refuses
type Verdict is Data:
  Go{hash: String, files: List<&2, K.File>, srcs: List<&2, String>}
  Wait{asks: List<&2, W.Ask>}
  Stop{why: String}

# the package, judged as the lock judges a hub package
def decide.body(verdict: W.Verdict, +hash: String) -> Verdict:
  match verdict:
    case W.Ok{fs, ss}:
      Go{hash, fs, ss}
    case W.No{why}:
      Stop{why}
    case W.Named{_ns}:
      Stop{"ez: " ++ hash ++ " was not answered with a package"}

# the package the hub served for the hash, or why it served none
def decide.got(answer: W.Answer, +hash: String, +world: A.World) -> Verdict:
  match answer:
    case W.Got{how, manifest, ss}:
      decide.body(W.hub.how(how, hash, manifest, ss), hash)
    case W.Miss{why}:
      Stop{W.hub.why(True{}, hash, A.hub(world), why)}
    case _:
      Stop{"ez: " ++ hash ++ " was not answered with a package"}

# the package, once it is asked for
def decide.pkg(got: Maybe<&2, W.Answer>, +hash: String, +world: A.World) -> Verdict:
  match got:
    case None{}:
      Wait{[W.Pkg{hash, L.Hub{}, A.hub(world)}]}
    case Some{answer}:
      decide.got(answer, hash, world)

# a `0x` name the hub answered, or an answer that names none
def decide.hash(ok: Bool, +hash: String, +world: A.World) -> Verdict:
  match ok:
    case True{}:
      decide.pkg(heard(A.hubs(world), hash), hash, world)
    case False{}:
      Stop{"ez: the hub at " ++ A.hub(world) ++ " names no package " ++ nv(world) ++
        " (it answered `" ++ hash ++ "`)"}

# why the hub gave no answer, without the `ez: ` a miss is said with
def unsaid(ez: Bool, +why: String) -> String:
  match ez:
    case True{}:
      String.drop(why, 4n)
    case False{}:
      why

# what the hub said the name names
def decide.said(answer: W.Answer, +world: A.World) -> Verdict:
  match answer:
    case W.Said{text}:
      +hash = String.trim(text)
      decide.hash(L.hash.ok(hash), hash, world)
    case W.Miss{+why}:
      Stop{"ez: the hub at " ++ A.hub(world) ++ " has no package " ++ nv(world) ++ " (" ++
        unsaid(String.starts_with(why, "ez: "), why) ++ ")"}
    case _:
      Stop{"ez: " ++ nv(world) ++ " was not answered with a hash"}

# the name, once it is asked of the hub
def decide.name(got: Maybe<&2, W.Answer>, +world: A.World) -> Verdict:
  match got:
    case None{}:
      Wait{[W.Name{nv(world), A.hub(world)}]}
    case Some{answer}:
      decide.said(answer, world)

# why the add is refused before anything is asked, "" when it is not: a ref
# and an entry both given, or a key the ledger refuses
def early(+world: A.World) -> String:
  Bool.pick(String,
    Bool.or(String.is_empty(A.ref(world)), String.is_empty(A.entry.arg(world))),
    Named.hub.why(A.deps(world), key(world), part(world), A.rename(world)),
    "ez: " ++ nv(world) ++ " pins its version; the word after it is the entry, " ++
      "and there is only one")

# a refusal the ledger alone decides
def decide.early(ok: Bool, +why: String, +world: A.World) -> Verdict:
  match ok:
    case True{}:
      decide.name(heard(A.hubs(world), nv(world)), world)
    case False{}:
      Stop{why}

# no ledger, or one that does not parse, is refused before anything else,
# with the reason every command that edits a ledger gives
def decide.read(read: M.Read, +world: A.World) -> Verdict:
  match read:
    case M.Bad{why}:
      Stop{"ez: " ++ M.show(M.Bad{why})}
    case M.Good{_m}:
      +e = early(world)
      decide.early(String.is_empty(e), e, world)

# where a World stands
def decide(+world: A.World) -> Verdict:
  decide.read(A.read(world), world)

# ---------------------------------------------------------------------------
# the entry

# whether a package holds a file at this path
def holds(fs: List<&2, K.File>, +at: String) -> Bool:
  match fs:
    case []:
      False{}
    case +h <> t:
      +rest = holds(t, at)
      Bool.or(String.eq(K.file.at(h), at), rest)

# a top-level `.bend` file: one with no directory in front of it
def top.one(+at: String) -> Bool:
  Bool.and(String.ends_with(at, ".bend"), Bool.not(String.contains(at, "/")))

# this file when it is a top-level `.bend` file, else the rest's. The rest
# arrives as a thunk, so the first one ends the scan.
def top.at(hit: Bool, +at: String, rest: Unit -> String) -> String:
  match hit:
    case True{}:
      at
    case False{}:
      rest(Unit{})

# the first top-level `.bend` file, in manifest order, "" for none
def top(fs: List<&2, K.File>) -> String:
  match fs:
    case []:
      ""
    case +h <> t:
      top.at(top.one(K.file.at(h)), K.file.at(h), _u => top(t))

# `main.bend` when the package holds one, else its first top-level file
def entry.main(held: Bool, fs: List<&2, K.File>) -> String:
  match held:
    case True{}:
      "main.bend"
    case False{}:
      top(fs)

# the entry a package is recorded with when none was asked for: its
# `main.bend`, else its first top-level `.bend` file, else none
def entry.of(+fs: List<&2, K.File>) -> String:
  entry.main(holds(fs, "main.bend"), fs)

# the entry asked for, or, when none was, the package's own
def entry.pick(none: Bool, +fs: List<&2, K.File>, +asked: String) -> String:
  match none:
    case True{}:
      entry.of(fs)
    case False{}:
      asked

# the entry recorded: the one asked for, else the package's own
def entry(+fs: List<&2, K.File>, +world: A.World) -> String:
  entry.pick(String.is_empty(asked(world)), fs, asked(world))

# ---------------------------------------------------------------------------
# the plan

# the dependency recorded for a package the hub named by this hash
def dep.of(+hash: String, +fs: List<&2, K.File>, +world: A.World) -> M.Dep:
  M.Dep{key(world), hash, entry(fs, world), M.Hub{nv(world)}}

# the ledger with the package added, once it is known to read back. A
# ledger that could not be written so that it reads back is refused
# (EZ-LED-4).
def outcome.fit(fit: Bool) -> P.Outcome:
  match fit:
    case True{}:
      P.Success{}
    case False{}:
      P.Refused{Rend.unrenderable()}

# an entry asked for must be in the package
def outcome.entry(held: Bool, fit: Bool, +at: String, +world: A.World) -> P.Outcome:
  match held:
    case True{}:
      outcome.fit(fit)
    case False{}:
      P.Refused{"ez: " ++ at ++ " is not in " ++ nv(world)}

# how an add ends once the package is in hand
def outcome.of(+hash: String, +fs: List<&2, K.File>, +world: A.World) -> P.Outcome:
  outcome.entry(Bool.or(String.is_empty(asked(world)), holds(fs, Path.norm(asked(world)))),
    Rend.renderable(Rend.add.keep(A.manifest.of(A.read(world)), dep.of(hash, fs, world))),
    asked(world), world)

# where the tree is laid: under `.ez/lib` when the entry it replaces is
# vendored, under BEND_LIB otherwise. A hub dependency is never vendored, so
# a name the ledger already records is laid under BEND_LIB like a new one.
def place.of(vend: Bool) -> P.Place:
  match vend:
    case True{}:
      P.Committed{}
    case False{}:
      P.Cache{}

# `.gitignore` written ahead of the rest when the allowlist changes it
def ignore.put(same: Bool, +next: String, rest: List<&2, P.Effect>) -> List<&2, P.Effect>:
  match same:
    case True{}:
      rest
    case False{}:
      P.Write{A.ignore.file(), next} <> rest

# the lines a person is told: the hash the name names, then, when there is
# an entry, the import line for it, the line `ez publish` prints with the
# name in place of the hash
def says(+hash: String, +entry: String, +world: A.World) -> List<&2, P.Effect>:
  Bool.pick(List<&2, P.Effect>, String.is_empty(entry), [P.Say{nv(world) ++ " is " ++ hash}],
    [P.Say{nv(world) ++ " is " ++ hash}, P.Say{Git.import.line(nv(world), Path.norm(entry))}])

# what an add of a package the hub served does: the tree laid, its name's
# file, ez.toml written, `.gitignore` when the allowlist changes, and what a
# person is told
def effects.of(
  +dep: M.Dep,
  +hash: String,
  +ls: List<&2, W.Source>,
  +manifest: M.Manifest,
  +world: A.World
) -> List<&2, P.Effect>:
  +old = M.find(A.deps.of(manifest), M.dep.name(dep))
  +next = I.sync(A.deps.of(Rend.add.keep(manifest, dep)), A.ignore(world))
  P.Lay{place.of(M.source.vendor(M.source.dep(old))), hash,
    List.append(&2, W.Source, ls, [W.Source{"manifest", W.manifest(ls)}])} <>
    (P.Name{nv(world), hash} <>
      (P.Write{A.toml(), Rend.show(Rend.add.keep(manifest, dep))} <>
        ignore.put(String.eq(next, A.ignore(world)), next,
          says(hash, M.dep.entry(dep), world))))

# a plan that refuses has no effect at all; its reason is how it ends
def seal(es: List<&2, P.Effect>, outcome: P.Outcome) -> P.Plan:
  match outcome:
    case P.Success{}:
      P.Plan{es, P.Success{}}
    case P.Refused{why}:
      P.Plan{[], P.Refused{why}}

# the plan once the package is in hand
def made(+hash: String, +fs: List<&2, K.File>, +ss: List<&2, String>, +world: A.World) -> P.Plan:
  seal(effects.of(dep.of(hash, fs, world), hash, W.laid(fs, ss),
      A.manifest.of(A.read(world)), world),
    outcome.of(hash, fs, world))

# the plan for where the World stands. One that still asks is a World the
# interpreter did not finish, and is refused rather than guessed at.
def plan.v(verdict: Verdict, +world: A.World) -> P.Plan:
  match verdict:
    case Go{hash, fs, ss}:
      made(hash, fs, ss, world)
    case Wait{_asks}:
      P.Plan{[], P.Refused{"ez: the hub was never asked what " ++ nv(world) ++ " names"}}
    case Stop{why}:
      P.Plan{[], P.Refused{why}}

# `ez add <name>@<version>` over a World
def plan(+world: A.World) -> P.Plan:
  plan.v(decide(world), world)

# the questions still open where the World stands
def asks.v(verdict: Verdict) -> List<&2, W.Ask>:
  match verdict:
    case Go{_hash, _fs, _ss}:
      []
    case Wait{asks}:
      asks
    case Stop{_why}:
      []

# the questions a World still leaves open
def wants(+world: A.World) -> List<&2, W.Ask>:
  asks.v(decide(world))

# ---------------------------------------------------------------------------
# law vocabulary

# whether a plan ends in a refusal
def refuses.plan(pl: P.Plan) -> Bool:
  P.Plan{_es, outcome} = pl
  match outcome:
    case P.Success{}:
      False{}
    case P.Refused{_why}:
      True{}

# whether `ez add <name>@<version>` refuses on a World
def refuses(+world: A.World) -> Bool:
  refuses.plan(plan(world))

# the hash and files a verdict carries, none when it carries no package
def verdict.hash(verdict: Verdict) -> String:
  match verdict:
    case Go{hash, _fs, _ss}:
      hash
    case Wait{_asks}:
      ""
    case Stop{_why}:
      ""

def verdict.files(verdict: Verdict) -> List<&2, K.File>:
  match verdict:
    case Go{_hash, fs, _ss}:
      fs
    case Wait{_asks}:
      []
    case Stop{_why}:
      []

# the hash the hub named, as the World answered it
def hash(+world: A.World) -> String:
  verdict.hash(decide(world))

# the package's files, as the hub served them
def files(+world: A.World) -> List<&2, K.File>:
  verdict.files(decide(world))

# the dependency `ez add <name>@<version>` records on a World
def added(+world: A.World) -> M.Dep:
  dep.of(hash(world), files(world), world)

# the hub a question names
def ask.hub(ask: W.Ask) -> String:
  match ask:
    case W.Pkg{_hash, _src, hub}:
      hub
    case W.Name{_nv, hub}:
      hub
    case W.Lock{}:
      ""

# whether every question names this hub
def asks.hub(as: List<&2, W.Ask>, +hub: String) -> Bool:
  match as:
    case []:
      True{}
    case h <> t:
      +rest = asks.hub(t, hub)
      Bool.and(String.eq(ask.hub(h), hub), rest)

# whether a question asks the hub what a name names
def names.one(ask: W.Ask) -> Bool:
  match ask:
    case W.Name{_nv, _hub}:
      True{}
    case _:
      False{}

# whether any question does
def names(as: List<&2, W.Ask>) -> Bool:
  match as:
    case []:
      False{}
    case h <> t:
      +rest = names(t)
      Bool.or(names.one(h), rest)

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

# every name's file a list of effects lays, in order
def names.laid(es: List<&2, P.Effect>) -> List<&2, L.Name>:
  match es:
    case []:
      []
    case e <> t:
      match e:
        case P.Name{nv, hash}:
          L.Name{nv, hash} <> names.laid(t)
        case _:
          names.laid(t)

# doctor/plan: `ez doctor` as a pure planner. It reads a World
# (doctor/world.bend) and returns either the questions it still needs
# answered (`step`) or a Plan: the lines to print and how the command ends
# (`plan`). The interpreter (doctor/run.bend) loops on `step`, answering each
# question by IO, until nothing is left to ask, then prints the plan.
#
# Doctor says what would stop this project from building. Each line reports
# what was found rather than a tick, because the useful answers here are
# values: which bend, which compiler, which packages are on disk, and which
# hashes the source and the ledger disagree about. A line that is a problem
# fails the command, as `cargo check` fails on the first thing it cannot
# build, though doctor goes on to say everything it found.
#
# The plan is lines said and an outcome, and nothing else: doctor writes no
# file, lays no tree and removes nothing (EZ-VEN-4). The questions it asks
# write nothing either: a program asked for its version, `ls` of the library,
# and git's listing of the tracked sources.
#
# The drift report is the ledger against the import lines. A package's `0x`
# hash is written in two places, the `[deps.<name>]` section of ez.toml and
# the `import 0x...` line that uses it, so the two can disagree. ez treats the
# ledger as the record and the import lines as the truth, and reports the
# disagreement both ways rather than rewriting anyone's source (EZ-VEN-5). An
# import line is one the lock reads as one: in the header of a `.bend` file
# git tracks outside `.ez/`, found by the package walk's own scan (`P.roots`),
# so doctor and `ez lock` never disagree about what the source imports. A
# ledger's `[tools.*]` pins are not dependencies, and nothing here reads them
# (EZ-LED-5).
#
# The Effect, Plan and Outcome types are the lock's (lock/plan.bend), as for
# the other commands.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./world.bend as DW
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/lock.bend as L
import ../manifest/manifest.bend as M
import ../ez/args.bend as Args

# one thing doctor looked at: what to print, and whether it is a problem
type Note is Data:
  Note{wrong: Bool, line: String}

# a count with its noun, kept in agreement
def plural(+count: Nat, one: String, many: String) -> String:
  Nat.show(count) ++ " " ++ Bool.pick(String, Nat.is_eq(count, 1n), one, many)

# the lines a run printed, or none when it failed, so a program's complaint on
# stderr is never mistaken for an answer
def answered(ok: Bool, +text: String) -> List<&2, String>:
  match ok:
    case True{}:
      Args.nonempty(String.lines(text))
    case False{}:
      []

# ---------------------------------------------------------------------------
# the toolchain

# the first line of what a program printed
def banner.of(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> _t:
      h

# a version banner, which is one line however many a program prints
def banner(text: String) -> String:
  banner.of(String.lines(text))

# what a version run said about the program it ran
def probe.note(ok: Bool, name: String, +text: String) -> Note:
  match ok:
    case True{}:
      Note{False{}, name ++ ": " ++ banner(text)}
    case False{}:
      Note{True{}, name ++ ": not on PATH"}

# what the answer to a version question says
def probe.answer(answer: DW.Answer, +name: String) -> Note:
  match answer:
    case DW.Printed{ok, text}:
      probe.note(ok, name, text)
    case DW.Listed{_l}:
      Note{True{}, name ++ ": not on PATH"}

# a program's line, once it was asked
def probe.heard(got: DW.Heard, +name: String) -> Note:
  match got:
    case DW.Heard{a}:
      probe.answer(a, name)
    case DW.Open{}:
      Note{True{}, name ++ ": not on PATH"}

# the C compiler the native lane will use: `$CC` when it is set, else `cc`.
# Same source and a different compiler is a different binary, so doctor names
# it.
def cc.name(+var: String) -> String:
  Bool.pick(String, String.is_empty(var), "cc", var)

# the programs doctor asks for their versions. bend's check report changed
# wording between 2.0.16 and 2.0.18, and the native lane needs a C compiler,
# so the version is the finding.
def programs(+cc: String) -> List<&2, String>:
  ["bend", cc.name(cc), "git"]

# every program's line
def probes(ns: List<&2, String>, +rs: List<&2, DW.Reply>) -> List<&2, Note>:
  match ns:
    case []:
      []
    case +h <> t:
      probe.heard(DW.heard(rs, DW.Probe{h}), h) <> probes(t, rs)

# ---------------------------------------------------------------------------
# the ledger and the lock

# the dependencies of a ledger that was read
def deps.of(manifest: M.Manifest) -> List<&2, M.Dep>:
  M.Manifest{_n, _e, _b, _h, ds, _ts} = manifest
  ds

# how many dependencies a ledger names; one that did not read names none
def deps.count(ledger: M.Read) -> Nat:
  match ledger:
    case M.Bad{_why}:
      0n
    case M.Good{m}:
      List.length(&2, M.Dep, deps.of(m))

# what the ledger turned out to be
def ledger.note(ledger: M.Read) -> Note:
  match ledger:
    case M.Bad{why}:
      Note{True{}, DW.toml() ++ ": " ++ why}
    case M.Good{m}:
      M.Manifest{n, e, _b, _h, ds, _ts} = m
      Note{False{}, DW.toml() ++ ": " ++ n ++ ", entry " ++ e ++ ", " ++
        plural(List.length(&2, M.Dep, ds), "dependency", "dependencies")}

# what the lock turned out to be: the packages it records, or why it could
# not be read, or no lock at all
type Locked is Data:
  Locked{hashes: List<&2, String>}
  Unread{why: String}
  Unlocked{}

# the verdict on a parse, with the answer in hand
def locked.pick(ok: Bool, why: String, ss: List<&2, T.Sect>) -> Locked:
  match ok:
    case True{}:
      Locked{L.hashes(ss)}
    case False{}:
      Unread{why}

# a lock that parsed, by the packages it records; one that did not, by why
def locked.parsed(toml: T.Toml) -> Locked:
  T.Toml{+bad, _name, _pairs, ss} = toml
  locked.pick(String.is_empty(bad), bad, ss)

# the lock's text, read
def locked.of(got: Maybe<&2, String>) -> Locked:
  match got:
    case None{}:
      Unlocked{}
    case Some{text}:
      locked.parsed(T.parse(text))

# the packages a lock records; none when it did not read or is not there
def locked.hashes(lk: Locked) -> List<&2, String>:
  match lk:
    case Locked{hs}:
      hs
    case Unread{_why}:
      []
    case Unlocked{}:
      []

# whether a ledger with this many dependencies needs a lock that names some
def lock.needs(deps: Nat) -> Bool:
  match deps:
    case 0n:
      False{}
    case 1n+_n:
      True{}

# whether the lock is a problem: it names no package while the ledger has
# dependencies it should have resolved. A project with no dependencies has
# nothing to lock, so a lock naming nothing, or no lock at all, is its due.
def lock.wrong(deps: Nat, hs: List<&2, String>) -> Bool:
  match hs:
    case []:
      lock.needs(deps)
    case _h <> _t:
      False{}

# what the lock amounts to. A lock that is there and does not parse is a
# problem whatever the ledger holds, since `ez fetch` refuses it, as cargo
# refuses a Cargo.lock it cannot read.
def lock.note(+deps: Nat, lk: Locked) -> Note:
  match lk:
    case Locked{+hs}:
      +wrong = lock.wrong(deps, hs)
      Note{wrong,
        DW.lockfile() ++ ": " ++ plural(List.length(&2, String, hs), "package", "packages") ++
        Bool.pick(String, wrong, " (it names none; run ez lock)", "")}
    case Unread{why}:
      Note{True{}, DW.lockfile() ++ ": " ++ why}
    case Unlocked{}:
      +wrong = lock.needs(deps)
      Note{wrong, DW.lockfile() ++ ": " ++
        Bool.pick(String, wrong, "none; run ez lock", "none, and nothing to lock")}

# ---------------------------------------------------------------------------
# BEND_LIB

# where the packages this build resolves against live. It is what ez itself
# passes to every bend it starts, so an unset BEND_LIB is not a finding: the
# default is `.ez/lib` beside the project, and what matters is what is in it.
def lib.at(+var: String) -> String:
  Bool.pick(String, String.is_empty(var), ".ez/lib", var)

# the names `ls` gave for the library, none when it gave none
def lib.have(got: DW.Heard) -> List<&2, String>:
  match got:
    case DW.Heard{a}:
      match a:
        case DW.Printed{ok, text}:
          answered(ok, text)
        case DW.Listed{_l}:
          []
    case DW.Open{}:
      []

# the rest of a scan only when this one was not it. `Bool.or` reduces both
# of its sides, so a scan written with it reads the whole list even when the
# first entry answers. The rest arrives as a thunk.
def has.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a list holds this string
def has(ss: List<&2, String>, +want: String) -> Bool:
  match ss:
    case []:
      False{}
    case +h <> t:
      has.step(String.eq(h, want), _u => has(t, want))

# a string kept when the other list lacks it
def missing.put(hit: Bool, item: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rest
    case False{}:
      item <> rest

# the strings of `xs` that `known` does not hold
def missing(xs: List<&2, String>, +known: List<&2, String>) -> List<&2, String>:
  match xs:
    case []:
      []
    case +h <> t:
      missing.put(has(known, h), h, missing(t, known))

# BEND_LIB judged against the lock: every package the lock names has to be on
# disk, because bend resolves a hub import during the check and a sandbox has
# no network to fall back on
def lib.said(all: Bool, +dir: String, +count: Nat, gone: List<&2, String>) -> Note:
  match all:
    case True{}:
      Note{False{}, "BEND_LIB: " ++ dir ++ ", all " ++
        plural(count, "locked package", "locked packages") ++ " present"}
    case False{}:
      Note{True{}, "BEND_LIB: " ++ dir ++ " lacks " ++ String.join(gone, " ") ++
        "; run ez fetch"}

# the verdict, once what is wanted and what is there are both known
def lib.judge(+dir: String, +want: List<&2, String>, have: List<&2, String>) -> Note:
  +gone = missing(want, have)
  lib.said(List.is_empty(&2, String, gone), dir, List.length(&2, String, want), gone)

# the library's line
def lib.note(+dir: String, +want: List<&2, String>, +rs: List<&2, DW.Reply>) -> Note:
  lib.judge(dir, want, lib.have(DW.heard(rs, DW.Lib{dir})))

# ---------------------------------------------------------------------------
# the drift report

# a head kept when the rest does not hold it again
def once.put(dup: Bool, item: String, rest: List<&2, String>) -> List<&2, String>:
  match dup:
    case True{}:
      rest
    case False{}:
      item <> rest

# every string of a list once, each where it last stands
def once(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case []:
      []
    case +h <> +t:
      once.put(has(t, h), h, once(t))

# every hub package the project's sources import, each once. These are the
# lock's roots: the header imports of every tracked `.bend` file outside
# `.ez/`, as the package walk scans them.
def imports(fs: List<&2, W.Source>) -> List<&2, String>:
  once(P.roots(fs))

# the hashes a ledger's dependencies name
def pinned(ds: List<&2, M.Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case h <> t:
      M.dep.hash(h) <> pinned(t)

# how a hash imported and not in the ledger reads
def unrecorded.line(+hash: String) -> String:
  "drift: " ++ hash ++ " is imported but ez.toml does not name it"

# every hash imported that the ledger does not name
def unrecorded(hs: List<&2, String>) -> List<&2, String>:
  match hs:
    case []:
      []
    case h <> t:
      unrecorded.line(h) <> unrecorded(t)

# how a ledger entry nobody imports reads
def unused.line(+dependency: M.Dep) -> String:
  "drift: " ++ M.dep.name(dependency) ++ " = " ++ M.dep.hash(dependency) ++
  " is in ez.toml but no import line uses it"

# a dependency reported when nothing imports it
def unused.put(hit: Bool, +dependency: M.Dep, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rest
    case False{}:
      unused.line(dependency) <> rest

# every dependency of the ledger that no import line uses
def unused(ds: List<&2, M.Dep>, +hs: List<&2, String>) -> List<&2, String>:
  match ds:
    case []:
      []
    case +h <> t:
      unused.put(has(hs, M.dep.hash(h)), h, unused(t, hs))

# both directions of the disagreement: a hash the source imports that the
# ledger never names, and a ledger entry no import line uses
def drift(+hs: List<&2, String>, +ds: List<&2, M.Dep>) -> List<&2, String>:
  List.append(&2, String, unrecorded(missing(hs, pinned(ds))), unused(ds, hs))

# every line of a report, each a problem
def flag(ls: List<&2, String>) -> List<&2, Note>:
  match ls:
    case []:
      []
    case h <> t:
      Note{True{}, h} <> flag(t)

# the report, or the one line that says there is nothing to report
def drift.notes(+hs: List<&2, String>, lines: List<&2, String>) -> List<&2, Note>:
  match lines:
    case []:
      [Note{False{}, "imports: " ++ plural(List.length(&2, String, hs), "package", "packages") ++
        " imported, every one named in ez.toml"}]
    case h <> t:
      flag(h <> t)

# the report over what git listed, or why it could not list
def listing.notes(listing: W.Listing, +ds: List<&2, M.Dep>) -> List<&2, Note>:
  match listing:
    case W.Listed{fs}:
      +hs = imports(fs)
      drift.notes(hs, drift(hs, ds))
    case W.Unlisted{_why}:
      [Note{True{}, "imports: git could not list the .bend files it tracks here"}]

# the report, once the sources were asked for
def sources.notes(got: DW.Heard, +ds: List<&2, M.Dep>) -> List<&2, Note>:
  match got:
    case DW.Heard{a}:
      match a:
        case DW.Listed{l}:
          listing.notes(l, ds)
        case DW.Printed{_ok, _text}:
          [Note{True{}, "imports: the sources were not read"}]
    case DW.Open{}:
      [Note{True{}, "imports: the sources were not read"}]

# the report over a ledger. One that did not read is its own problem, and
# there is nothing to compare the source with.
def imports.notes(ledger: M.Read, got: DW.Heard) -> List<&2, Note>:
  match ledger:
    case M.Bad{_why}:
      [Note{False{}, "imports: not compared, since ez.toml was not read"}]
    case M.Good{m}:
      sources.notes(got, deps.of(m))

# ---------------------------------------------------------------------------
# the plan

# the ledger as doctor sees it: its package, its entry and its dependencies.
# Its `[tools.*]` pins are not dependencies, and nothing doctor says or asks
# turns on them, so they are dropped before anything is decided (EZ-LED-5).
def ledger.seen(ledger: M.Read) -> M.Read:
  match ledger:
    case M.Bad{why}:
      M.Bad{why}
    case M.Good{m}:
      M.Manifest{n, e, b, h, ds, _ts} = m
      M.Good{M.Manifest{n, e, b, h, ds, []}}

# the toolchain, the ledger, the lock and the library, each on its line
def head.notes(
  +ledger: M.Read,
  +cc: String,
  +lib: String,
  lock: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>
) -> List<&2, Note>:
  +lk = locked.of(lock)
  List.append(&2, Note, probes(programs(cc), rs),
    [ledger.note(ledger), lock.note(deps.count(ledger), lk),
      lib.note(lib.at(lib), locked.hashes(lk), rs)])

# every line doctor says, in order: the toolchain, the ledger, the lock, the
# library, and last the drift report over the sources as they were heard
def notes.of(
  +ledger: M.Read,
  got: DW.Heard,
  +cc: String,
  +lib: String,
  lock: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>
) -> List<&2, Note>:
  List.append(&2, Note, head.notes(ledger, cc, lib, lock, rs), imports.notes(ledger, got))

# whether a note is a problem
def note.wrong(finding: Note) -> Bool:
  Note{w, _l} = finding
  w

# whether anything found was a problem. The rest arrives as a thunk and only
# the arm that wants it applies it.
def wrong(ns: List<&2, Note>) -> Bool:
  match ns:
    case []:
      False{}
    case h <> t:
      has.step(note.wrong(h), _u => wrong(t))

# each line said
def says(ns: List<&2, Note>) -> List<&2, P.Effect>:
  match ns:
    case []:
      []
    case Note{_w, l} <> t:
      P.Say{l} <> says(t)

# a problem must fail the command, or a script around it learns nothing. The
# lines already said what the problem is.
def outcome.of(bad: Bool) -> P.Outcome:
  match bad:
    case True{}:
      P.Refused{""}
    case False{}:
      P.Success{}

# the plan for these notes: every line said, and the command failed when one
# of them is a problem
def plan.notes(+ns: List<&2, Note>) -> P.Plan:
  P.Plan{says(ns), outcome.of(wrong(ns))}

# the plan over what a World read, field by field
def plan.of(
  +ledger: M.Read,
  +cc: String,
  +lib: String,
  lock: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>
) -> P.Plan:
  plan.notes(notes.of(ledger, DW.heard(rs, DW.Sources{}), cc, lib, lock, rs))

# `ez doctor` over a World
def plan(+world: DW.World) -> P.Plan:
  plan.of(ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world),
    DW.replies(world))

# whether a plan ends in a refusal
def refuses.plan(pl: P.Plan) -> Bool:
  P.Plan{_es, outcome} = pl
  match outcome:
    case P.Success{}:
      False{}
    case P.Refused{_why}:
      True{}

# whether `ez doctor` fails on a World
def refuses(+world: DW.World) -> Bool:
  refuses.plan(plan(world))

# ---------------------------------------------------------------------------
# what is still to ask

# a question kept when it has no answer yet
def open.put(got: DW.Heard, ask: DW.Ask, rest: List<&2, DW.Ask>) -> List<&2, DW.Ask>:
  match got:
    case DW.Heard{_a}:
      rest
    case DW.Open{}:
      ask <> rest

# the questions of a list that have no answer yet
def open(asks: List<&2, DW.Ask>, +rs: List<&2, DW.Reply>) -> List<&2, DW.Ask>:
  match asks:
    case []:
      []
    case +h <> t:
      open.put(DW.heard(rs, h), h, open(t, rs))

# a version question for every program
def probe.asks(ns: List<&2, String>) -> List<&2, DW.Ask>:
  match ns:
    case []:
      []
    case h <> t:
      DW.Probe{h} <> probe.asks(t)

# the library is looked in only when the lock names a package to look for
def lib.asks(+dir: String, hs: List<&2, String>) -> List<&2, DW.Ask>:
  match hs:
    case []:
      []
    case _h <> _t:
      [DW.Lib{dir}]

# the sources are read only when there is a ledger to compare them with
def sources.asks(ledger: M.Read) -> List<&2, DW.Ask>:
  match ledger:
    case M.Bad{_why}:
      []
    case M.Good{_m}:
      [DW.Sources{}]

# every question doctor asks on what a World read
def asks.of(ledger: M.Read, +cc: String, +lib: String, lock: Maybe<&2, String>) -> List<&2, DW.Ask>:
  List.append(&2, DW.Ask, probe.asks(programs(cc)),
    List.append(&2, DW.Ask, lib.asks(lib.at(lib), locked.hashes(locked.of(lock))),
      sources.asks(ledger)))

# the questions still open, or the plan once there are none
type Step is Data:
  Asking{asks: List<&2, DW.Ask>}
  Run{plan: P.Plan}

# the step, once the open questions are known
def step.asks(
  asks: List<&2, DW.Ask>,
  +ledger: M.Read,
  +cc: String,
  +lib: String,
  lock: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>
) -> Step:
  match asks:
    case []:
      Run{plan.of(ledger, cc, lib, lock, rs)}
    case h <> t:
      Asking{h <> t}

# the step over what a World read, field by field. Every question depends
# only on what the World read, so doctor asks in one round.
def step.of(
  +ledger: M.Read,
  +cc: String,
  +lib: String,
  +lock: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>
) -> Step:
  step.asks(open(asks.of(ledger, cc, lib, lock), rs), ledger, cc, lib, lock, rs)

# what the interpreter does next on a World
def step(+world: DW.World) -> Step:
  step.of(ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world),
    DW.replies(world))

# the questions a World still leaves open
def wants(+world: DW.World) -> List<&2, DW.Ask>:
  +ledger = ledger.seen(DW.read(world))
  open(asks.of(ledger, DW.cc(world), DW.lib(world), DW.lock(world)), DW.replies(world))

# ---------------------------------------------------------------------------
# law vocabulary: ez never calls these

# whether an effect says this line
def said.one(effect: P.Effect, +line: String) -> Bool:
  match effect:
    case P.Say{text}:
      String.eq(text, line)
    case P.Write{_at, _text}:
      False{}
    case P.Lay{_place, _hash, _files}:
      False{}
    case P.Drop{_hash}:
      False{}

# whether a list of effects says this line
def said.in(es: List<&2, P.Effect>, +line: String) -> Bool:
  match es:
    case []:
      False{}
    case e <> t:
      has.step(said.one(e, line), _u => said.in(t, line))

# whether a plan says this line
def said(pl: P.Plan, +line: String) -> Bool:
  P.Plan{es, _outcome} = pl
  said.in(es, line)

# the drift report doctor makes of a World's sources against a ledger's
# dependencies
def drift.of(fs: List<&2, W.Source>, +ds: List<&2, M.Dep>) -> List<&2, String>:
  +hs = imports(fs)
  drift(hs, ds)

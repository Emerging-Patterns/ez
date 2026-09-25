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
# git's listing of the tracked sources, and a package's files read from under
# BEND_LIB.
#
# A named import, `import <name>@<version>/...`, is read the same way: its
# name is what the import line names, reported when no dependency of the
# ledger records it, and a dependency recorded by a name is used when an
# import line names it by that name or by its hash. Each name the lock
# records has its file under `BEND_LIB/names`, which bend reads the name's
# hash from before it asks the hub; one missing, or naming another hash, is
# reported with the library, and fails the command.
#
# The drift report is the ledger against the import lines. A package's `0x`
# hash is written in two places, the `[deps.<name>]` section of ez.toml and
# the `import 0x...` line that uses it, so the two can disagree. ez treats the
# ledger as the record and the import lines as the truth, and reports the
# disagreement both ways rather than rewriting anyone's source (EZ-VEN-5). An
# import line is one the lock reads as one: in the header of a `.bend` file
# git tracks outside `.ez/`, found by the package walk's own scan (`P.roots`),
# so doctor and `ez lock` never disagree about what the source imports. A
# ledger's `[tools.*]` pins are not dependencies, and the report never reads
# them (EZ-LED-5).
#
# The lock is checked the way `cargo --locked` and `uv lock --check` check
# one, without the network: doctor puts a plain `ez lock` to the lock's own
# planner (lock/plan.bend), over the ledger as it is, tools and all, the
# sources git lists, and the trees BEND_LIB holds, and compares the text it
# would write with ez.lock.toml byte for byte (EZ-VEN-6). So every hash,
# source, file sum and tool pin the lock records is checked, by the code that
# writes them. A package the lock would read and BEND_LIB lacks is one doctor
# cannot see, and the lock is then said to be unchecked rather than guessed
# at; that, a lock ez lock would refuse to write, and a lock it would write
# otherwise, each fail the command.
#
# The Effect, Plan and Outcome types are the lock's (lock/plan.bend), as for
# the other commands.
import Base
import ../toml/toml.bend as T
import ./world.bend as DW
import ../lock/plan.bend as P
import ../lock/world.bend as W
import ../lock/lock.bend as L
import ../ledger/manifest.bend as M
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
    case _:
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
  M.Manifest{_n, _e, _b, _h, _pa, _pv, ds, _ts} = manifest
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
      M.Manifest{n, e, _b, _h, _pa, _pv, ds, _ts} = m
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
        case _:
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

# the names the lock records, with the hash each names; none when there is
# no lock, or when it does not read
def lock.names(lock: Maybe<&2, String>) -> List<&2, L.Name>:
  match lock:
    case None{}:
      []
    case Some{text}:
      L.names.read(text)

# what a name's file says against the lock: nothing when it holds the lock's
# hash, as bend trims it, and the fault otherwise
def name.held(same: Bool, +nv: String, +hash: String, +was: String) -> List<&2, String>:
  match same:
    case True{}:
      []
    case False{}:
      ["names/" ++ nv ++ " names " ++ was ++ " where the lock names " ++ hash]

def name.got(got: Maybe<&2, String>, +nv: String, +hash: String) -> List<&2, String>:
  match got:
    case None{}:
      ["names/" ++ nv ++ " is not there"]
    case Some{text}:
      +was = String.trim(text)
      name.held(String.eq(was, hash), nv, hash, was)

def name.heard(got: DW.Heard, +nv: String, +hash: String) -> List<&2, String>:
  match got:
    case DW.Heard{a}:
      match a:
        case DW.Held{m}:
          name.got(m, nv, hash)
        case _:
          ["names/" ++ nv ++ " was not read"]
    case DW.Open{}:
      ["names/" ++ nv ++ " was not read"]

# every name of the lock whose file under BEND_LIB is missing, or names
# another hash than the lock does, which bend would read instead of asking
# the hub
def names.wrong(ns: List<&2, L.Name>, +rs: List<&2, DW.Reply>) -> List<&2, String>:
  match ns:
    case []:
      []
    case L.Name{+nv, +hash} <> t:
      List.append(&2, String, name.heard(DW.heard(rs, DW.Name{nv}), nv, hash), names.wrong(t, rs))

# what the library holds of the lock's names, said after its packages
def names.said(+count: Nat) -> String:
  match count:
    case 0n:
      ""
    case 1n+_p:
      " with their " ++ plural(count, "name", "names")

# what is wrong with the library, each fault in its place
def lib.faults(gone: List<&2, String>, bad: List<&2, String>) -> String:
  match gone:
    case []:
      String.join(bad, "; ")
    case _g <> _t:
      match bad:
        case []:
          "lacks " ++ String.join(gone, " ")
        case _b <> _u:
          "lacks " ++ String.join(gone, " ") ++ "; " ++ String.join(bad, "; ")

# BEND_LIB judged against the lock: every package the lock names has to be on
# disk, because bend resolves a hub import during the check and a sandbox has
# no network to fall back on, and so does every name's file, since bend
# would otherwise ask the hub what the name names
def lib.said(all: Bool, +dir: String, +count: Nat, +names: Nat, gone: List<&2, String>, bad: List<&2, String>) -> Note:
  match all:
    case True{}:
      Note{False{}, "BEND_LIB: " ++ dir ++ ", all " ++
        plural(count, "locked package", "locked packages") ++ " present" ++ names.said(names)}
    case False{}:
      Note{True{}, "BEND_LIB: " ++ dir ++ " " ++ lib.faults(gone, bad) ++ "; run ez fetch"}

# the verdict, once what is wanted and what is there are both known
def lib.judge(
  +dir: String,
  +want: List<&2, String>,
  +ns: List<&2, L.Name>,
  have: List<&2, String>,
  +rs: List<&2, DW.Reply>
) -> Note:
  +gone = missing(want, have)
  +bad = names.wrong(ns, rs)
  lib.said(Bool.and(List.is_empty(&2, String, gone), List.is_empty(&2, String, bad)), dir,
    List.length(&2, String, want), List.length(&2, L.Name, ns), gone, bad)

# the library's line
def lib.note(+dir: String, +want: List<&2, String>, +ns: List<&2, L.Name>, +rs: List<&2, DW.Reply>) -> Note:
  lib.judge(dir, want, ns, lib.have(DW.heard(rs, DW.Lib{dir})), rs)

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

# every hub package the project's sources import, each once, by hash and by
# name. These are the lock's roots: the header imports of every tracked
# `.bend` file outside `.ez/`, as the package walk scans them.
def imports(+fs: List<&2, W.Source>) -> List<&2, String>:
  once(List.append(&2, String, P.roots(fs), P.roots.named(fs)))

# a dependency's name, when the ledger records it by one
def pinned.at(none: Bool, nv: String, rest: List<&2, String>) -> List<&2, String>:
  match none:
    case True{}:
      rest
    case False{}:
      nv <> rest

def pinned.nv(+nv: String, rest: List<&2, String>) -> List<&2, String>:
  pinned.at(String.is_empty(nv), nv, rest)

# the hashes a ledger's dependencies name, and the names it records them by
def pinned(ds: List<&2, M.Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case +h <> t:
      M.dep.hash(h) <> pinned.nv(M.source.nv(M.source.dep(h)), pinned(t))

# whether an import line names a dependency, by its hash or by its name
def used(+hs: List<&2, String>, +dependency: M.Dep) -> Bool:
  +nv = M.source.nv(M.source.dep(dependency))
  Bool.or(has(hs, M.dep.hash(dependency)),
    Bool.and(Bool.not(String.is_empty(nv)), has(hs, nv)))

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
      unused.put(used(hs, h), h, unused(t, hs))

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
        case _:
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
# the lock against the lock `ez lock` would write

# how a tree read from BEND_LIB arrived, as the lock judges it. A git
# package's tree under BEND_LIB is one `ez lock` reads from there too. A hub
# package's is one `ez lock` would have the hub serve: its name is the digest
# of its manifest and each file is checked against its sum, so bytes that pass
# are the bytes the hub serves under that name, and bytes that do not are
# refused either way.
def tree.how(src: L.Src) -> W.How:
  match src:
    case L.Hub{}:
      W.Served{}
    case L.Git{_url, _rev, _entry, _root, _nar, _tag}:
      W.Lib{}

# the source a lock question names
def ask.src(ask: W.Ask) -> L.Src:
  match ask:
    case W.Pkg{_hash, src, _hub}:
      src
    case W.Name{_nv, _hub}:
      L.Hub{}
    case W.Lock{}:
      L.Hub{}

# a tree BEND_LIB held, as the answer the lock reads, ahead of the rest. One
# it did not hold answers nothing, so the lock goes on asking for it.
def tree.put(+ask: W.Ask, answer: DW.Answer, rest: List<&2, W.Reply>) -> List<&2, W.Reply>:
  match answer:
    case DW.Laid{manifest, ss}:
      W.Reply{ask, W.Got{tree.how(ask.src(ask)), manifest, ss}} <> rest
    case _:
      rest

# a reply kept when it answers a lock question
def tree.reply(ask: DW.Ask, answer: DW.Answer, rest: List<&2, W.Reply>) -> List<&2, W.Reply>:
  match ask:
    case DW.Tree{a}:
      tree.put(a, answer, rest)
    case _:
      rest

# every tree BEND_LIB held, as the lock's answers
def trees(rs: List<&2, DW.Reply>) -> List<&2, W.Reply>:
  match rs:
    case []:
      []
    case DW.Reply{ask, answer} <> t:
      tree.reply(ask, answer, trees(t))

# the lock's text, "" when there is none, as the lock's own question reads it
def lock.text(lock: Maybe<&2, String>) -> String:
  match lock:
    case None{}:
      ""
    case Some{text}:
      text

# a name's file BEND_LIB held, as the answer the lock reads for the name,
# ahead of the rest. One it did not hold answers nothing, so the lock goes on
# asking for it.
def name.put(+nv: String, got: Maybe<&2, String>, rest: List<&2, W.Reply>) -> List<&2, W.Reply>:
  match got:
    case Some{text}:
      W.Reply{W.Name{nv, "BEND_LIB/names"}, W.Said{text}} <> rest
    case None{}:
      rest

# a reply kept when it answers a name's question
def name.reply(ask: DW.Ask, answer: DW.Answer, rest: List<&2, W.Reply>) -> List<&2, W.Reply>:
  match ask:
    case DW.Name{nv}:
      match answer:
        case DW.Held{got}:
          name.put(nv, got, rest)
        case _:
          rest
    case _:
      rest

# every name's file BEND_LIB held, as the lock's answers
def held(rs: List<&2, DW.Reply>) -> List<&2, W.Reply>:
  match rs:
    case []:
      []
    case DW.Reply{ask, answer} <> t:
      name.reply(ask, answer, held(t))

# the World doctor puts to the lock planner: a plain lock over the ledger's
# text as it is, the sources as git listed them, the lock as it is, which
# answers the lock's question about the names it records, every tree
# BEND_LIB held, and every name's file it held, never the network. The
# directory a lock runs in only anchors the questions it asks, which doctor
# answers by hash from BEND_LIB, so it is left empty.
def relock.world(
  ledger: Maybe<&2, String>,
  lock: Maybe<&2, String>,
  listing: W.Listing,
  +rs: List<&2, DW.Reply>
) -> W.World:
  W.World{W.Args{False{}, "", ""}, ledger, listing,
    List.append(&2, W.Reply, trees(rs), W.Reply{W.Lock{}, W.Locked{lock.text(lock)}} <> held(rs)),
    []}

# that World, over the sources as a list of files
def relock(+world: DW.World, fs: List<&2, W.Source>) -> W.World:
  relock.world(DW.ledger(world), DW.lock(world), W.Listed{fs}, DW.replies(world))

# the line for a lock `ez lock` would write as it is
def fresh.line() -> String:
  DW.lockfile() ++ ": up to date with ez.toml and the sources"

# the line for one it would write otherwise
def stale.line() -> String:
  DW.lockfile() ++ ": out of date with ez.toml and the sources; run ez lock"

# the verdict, once the two texts were compared
def fresh.said(same: Bool) -> Note:
  match same:
    case True{}:
      Note{False{}, fresh.line()}
    case False{}:
      Note{True{}, stale.line()}

# the lock against what the lock planner decided: the text it would write, or
# why it would write none
def fresh.doc(doc: P.Doc, +text: String) -> Note:
  match doc:
    case P.Doc{made}:
      fresh.said(String.eq(made, text))
    case P.Stop{why}:
      Note{True{}, DW.lockfile() ++ ": not checked, since ez lock refuses here: " ++ why}

# the hashes of lock questions
def ask.hashes(as: List<&2, W.Ask>) -> List<&2, String>:
  match as:
    case []:
      []
    case h <> t:
      W.ask.hash(h) <> ask.hashes(t)

# the lock, once every name the lock planner asks about is known: when none
# is left, what it decided; when some are, their files are not under
# BEND_LIB, and doctor does not ask the hub for them
def fresh.named(as: List<&2, W.Ask>, +lw: W.World, +text: String) -> Note:
  match as:
    case []:
      fresh.doc(P.decide(W.inputs(lw)), text)
    case h <> t:
      Note{True{}, DW.lockfile() ++ ": not checked, since BEND_LIB lacks names/" ++
        String.join(ask.hashes(h <> t), " names/") ++ " and doctor does not use the network"}

# the lock, once every question the lock planner asks is known: when none is
# left, its names, then what it decided; when some are, they are about
# packages BEND_LIB does not hold, and doctor does not ask the network for
# them
def fresh.away(as: List<&2, W.Ask>, +lw: W.World, +text: String) -> Note:
  match as:
    case []:
      fresh.named(P.wants.names(lw), lw, text)
    case h <> t:
      Note{True{}, DW.lockfile() ++ ": not checked, since BEND_LIB lacks " ++
        String.join(ask.hashes(h <> t), " ") ++ " and doctor does not use the network"}

# the check over the sources git listed. Sources git could not list are the
# drift report's to say.
def fresh.listing(+world: DW.World, listing: W.Listing, +text: String) -> List<&2, Note>:
  match listing:
    case W.Listed{fs}:
      +lw = relock(world, fs)
      [fresh.away(P.wants(lw), lw, text)]
    case W.Unlisted{_why}:
      []

# the check, once the sources were heard. They are asked for only when the
# ledger reads, so a ledger that does not is not checked against.
def fresh.heard(got: DW.Heard, +world: DW.World, +text: String) -> List<&2, Note>:
  match got:
    case DW.Heard{a}:
      match a:
        case DW.Listed{l}:
          fresh.listing(world, l, text)
        case _:
          []
    case DW.Open{}:
      []

# the check over a lock that is there. With no lock there is nothing to
# compare, and the lock's own line says whether that is a problem.
def fresh.notes(lock: Maybe<&2, String>, +world: DW.World) -> List<&2, Note>:
  match lock:
    case None{}:
      []
    case Some{text}:
      fresh.heard(DW.sources(world), world, text)

# what doctor says of the lock against the lock `ez lock` would write
def checked(+world: DW.World) -> List<&2, Note>:
  fresh.notes(DW.lock(world), world)

# each lock question, put to BEND_LIB
def trees.asked(as: List<&2, W.Ask>) -> List<&2, DW.Ask>:
  match as:
    case []:
      []
    case h <> t:
      DW.Tree{h} <> trees.asked(t)

# each of the lock's name questions, put to BEND_LIB as the name's file. The
# lock's own question never reaches here, since the World answers it.
def names.asked(as: List<&2, W.Ask>) -> List<&2, DW.Ask>:
  match as:
    case []:
      []
    case h <> t:
      DW.Name{W.ask.hash(h)} <> names.asked(t)

# the lock questions over the sources git listed, packages and then names
def trees.world(+lw: W.World) -> List<&2, DW.Ask>:
  List.append(&2, DW.Ask, trees.asked(P.wants(lw)), names.asked(P.wants.names(lw)))

def trees.listing(
  ledger: Maybe<&2, String>,
  lock: Maybe<&2, String>,
  listing: W.Listing,
  rs: List<&2, DW.Reply>
) -> List<&2, DW.Ask>:
  match listing:
    case W.Listed{fs}:
      trees.world(relock.world(ledger, lock, W.Listed{fs}, rs))
    case W.Unlisted{_why}:
      []

# the lock questions, once the sources were heard
def trees.heard(
  got: DW.Heard,
  ledger: Maybe<&2, String>,
  lock: Maybe<&2, String>,
  rs: List<&2, DW.Reply>
) -> List<&2, DW.Ask>:
  match got:
    case DW.Heard{a}:
      match a:
        case DW.Listed{l}:
          trees.listing(ledger, lock, l, rs)
        case _:
          []
    case DW.Open{}:
      []

# every package and name the lock planner asks about, while there is a lock
# to check. These depend on the sources and on the trees already read, so
# they come in rounds, as the lock's own do.
def trees.of(
  ledger: Maybe<&2, String>,
  lock: Maybe<&2, String>,
  held: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>
) -> List<&2, DW.Ask>:
  match lock:
    case None{}:
      []
    case Some{_text}:
      trees.heard(DW.heard(rs, DW.Sources{}), ledger, held, rs)

# ---------------------------------------------------------------------------
# the plan

# the ledger as doctor sees it: its package, its entry and its dependencies.
# Its `[tools.*]` pins are not dependencies, so they are dropped before
# anything but the lock check is decided (EZ-LED-5). The lock check reads the
# ledger's text as `ez lock` does, since the lock records the pins.
def ledger.seen(ledger: M.Read) -> M.Read:
  match ledger:
    case M.Bad{why}:
      M.Bad{why}
    case M.Good{m}:
      M.Manifest{n, e, b, h, pa, pv, ds, _ts} = m
      M.Good{M.Manifest{n, e, b, h, pa, pv, ds, []}}

# the toolchain, the ledger, the lock and the library, each on its line, and
# the lock check's line after them
def head.notes(
  +ledger: M.Read,
  +cc: String,
  +lib: String,
  +lock: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>,
  cs: List<&2, Note>
) -> List<&2, Note>:
  +lk = locked.of(lock)
  List.append(&2, Note, probes(programs(cc), rs),
    List.append(&2, Note,
      [ledger.note(ledger), lock.note(deps.count(ledger), lk),
        lib.note(lib.at(lib), locked.hashes(lk), lock.names(lock), rs)], cs))

# every line doctor says, in order: the toolchain, the ledger, the lock, the
# library, the lock check, and last the drift report over the sources as they
# were heard
def notes.of(
  +ledger: M.Read,
  got: DW.Heard,
  +cc: String,
  +lib: String,
  lock: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>,
  cs: List<&2, Note>
) -> List<&2, Note>:
  List.append(&2, Note, head.notes(ledger, cc, lib, lock, rs, cs), imports.notes(ledger, got))

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

# the plan over what a World read, field by field, with the lock check's
# lines
def plan.of(
  +ledger: M.Read,
  +cc: String,
  +lib: String,
  lock: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>,
  cs: List<&2, Note>
) -> P.Plan:
  plan.notes(notes.of(ledger, DW.heard(rs, DW.Sources{}), cc, lib, lock, rs, cs))

# `ez doctor` over a World
def plan(+world: DW.World) -> P.Plan:
  plan.of(ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world),
    DW.replies(world), checked(world))

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

# a question for every name's file the lock records
def names.asks(ns: List<&2, L.Name>) -> List<&2, DW.Ask>:
  match ns:
    case []:
      []
    case L.Name{nv, _hash} <> t:
      DW.Name{nv} <> names.asks(t)

# every question doctor asks on what a World read, besides the lock check's
def asks.of(ledger: M.Read, +cc: String, +lib: String, +lock: Maybe<&2, String>) -> List<&2, DW.Ask>:
  List.append(&2, DW.Ask, probe.asks(programs(cc)),
    List.append(&2, DW.Ask, lib.asks(lib.at(lib), locked.hashes(locked.of(lock))),
      List.append(&2, DW.Ask, names.asks(lock.names(lock)), sources.asks(ledger))))

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
  +rs: List<&2, DW.Reply>,
  cs: List<&2, Note>
) -> Step:
  match asks:
    case []:
      Run{plan.of(ledger, cc, lib, lock, rs, cs)}
    case h <> t:
      Asking{h <> t}

# the step over what a World read, field by field, with the lock check's
# questions and lines. The first round asks everything but the lock check's
# trees, which follow the sources and each other, as the lock's own questions
# do.
def step.of(
  +ledger: M.Read,
  +cc: String,
  +lib: String,
  +lock: Maybe<&2, String>,
  +rs: List<&2, DW.Reply>,
  ts: List<&2, DW.Ask>,
  cs: List<&2, Note>
) -> Step:
  step.asks(open(List.append(&2, DW.Ask, asks.of(ledger, cc, lib, lock), ts), rs),
    ledger, cc, lib, lock, rs, cs)

# what the interpreter does next on a World
def step(+world: DW.World) -> Step:
  step.of(ledger.seen(DW.read(world)), DW.cc(world), DW.lib(world), DW.lock(world),
    DW.replies(world), trees.of(DW.ledger(world), DW.lock(world), DW.lock(world), DW.replies(world)),
    checked(world))

# the questions a World still leaves open
def wants(+world: DW.World) -> List<&2, DW.Ask>:
  +ledger = ledger.seen(DW.read(world))
  open(List.append(&2, DW.Ask, asks.of(ledger, DW.cc(world), DW.lib(world), DW.lock(world)),
    trees.of(DW.ledger(world), DW.lock(world), DW.lock(world), DW.replies(world))), DW.replies(world))

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
    case P.Name{_nv, _hash}:
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

# ez/test: the test runner. Bend has none, so a test is a `*/tests/*.bend` file
# that prints, and states in a `#|` trailer the lines its run must print. Every
# unit test runs twice: on the JS lane, where bend interprets it, and on the
# native CPU lane, where it is compiled to a binary first. A lane disagreeing
# with the trailer is a failure, and any failure is a non-zero exit.
#
# A lane is one `bend` a project, not one a test. bend has no incremental
# compile, so every build pays for the whole import closure, and a project's
# tests import nearly the same one; `ez/gate.bend` writes the aggregate that
# pays it once, and this splits the run's output back up so each test still
# answers for its own trailer. A lane that has already held over exactly the
# files it reads is not run again either, which `ez/cache.bend` keys and
# `--full` ignores.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ./args.bend as Args
import ./env.bend as Env
import ./cap.bend as Cap
import ./cache.bend as C
import ./gate.bend as G
import ./sorted.bend as Sort
import ./quiet.bend as Q
import ./clock.bend as Clock

# how many comparisons were made, and how many of them held
type Tally is Data:
  Tally{pass: Nat, total: Nat}

# every line of a block, indented under the heading that introduces it
def indent.go(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case h <> t:
      ("    " ++ h ++ "\n") <> indent.go(t)

# a block of text, indented
def indent(text: String) -> String:
  String.concat(indent.go(String.lines(text)))

# a comparison that held says nothing. One that did not prints both sides in
# full: a diff is real work in Bend, and for a handful of short lines the pair
# reads better than one would.
def say(ok: Bool, name: String, want: String, got: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.write("FAIL: " ++ name ++ "\n  expected:\n" ++ indent(want) ++
        "  observed:\n" ++ indent(got))

# one more comparison, and one more pass when it held
def tally.go(ok: Bool, p: Nat, n: Nat) -> Tally:
  match ok:
    case True{}:
      Tally{(1n + p : Nat), (1n + n : Nat)}
    case False{}:
      Tally{p, (1n + n : Nat)}

# the tally with this comparison's verdict in it
def tally(ok: Bool, t: Tally) -> Tally:
  Tally{p, n} = t
  tally.go(ok, p, n)

# what was wanted against what happened, reported and counted
def check(name: String, +wanted: String, +got: String, t: Tally) -> IO(Tally):
  do IO<Tally>:
    say(String.eq(wanted, got), name, wanted, got)
    return tally(String.eq(wanted, got), t)

# the first line of a run's output, which is a proof's whole verdict
def head.of(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> _t:
      h

# the first line of some text
def head(text: String) -> String:
  head.of(String.lines(text))

# a test whose header says so is not run on the JS lane, which overflows its
# stack on a string over about 65 KB. The native lane has no such limit.
#
# The header is a line and is matched as one. A whole-file substring search
# reads `# lanes: native` inside a string literal as a header — which is
# exactly what a test of a tool that reads headers carries — and drops the
# file from the lane. Nothing fails, the run is simply one comparison
# shorter, and a green count over fewer tests than the tree holds is the
# worst answer a gate can give.
def js_lane(+text: String) -> Bool:
  Bool.not(G.headed(text, "# lanes: native"))

# whether a test is one of the unit tests, which live in a `tests/` beside the
# code they are about. The end-to-end tests are the top-level `tests/`, and
# what they drive is git, nix and bend itself: compiling the driver a second
# time would run those tools twice over to learn nothing new about them. They
# are also the tests an aggregate has no business holding — each one wants its
# own process, its own scratch directory and its own ports.
def unit(+path: String) -> Bool:
  Bool.and(Bool.not(String.starts_with(G.rel(path), "tests/")),
    Bool.not(String.is_empty(G.proj(path))))

# whether this test belongs to the half being gathered
def keep(want_unit: Bool, +is_unit: Bool) -> Bool:
  Bool.pick(Bool, want_unit, is_unit, Bool.not(is_unit))

# the unit tests, or everything that is not one
def some(ts: List<&2, String>, +want_unit: Bool) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = some(t, want_unit)
      Bool.pick(List<&2, String>, keep(want_unit, unit(h)), h <> more, more)

# whether an end-to-end test is one this run will take. `--unit-only` says no
# to all of them, for a caller that has a sandbox rather than a machine: the
# top-level `tests/` start real git daemons, publish to a real hub and shell
# out to `nix-build`, and a sandbox has no network, no nix daemon and no ports
# to give them. The unit tests, which read and write nothing outside the tree,
# are unaffected. This is selection and nothing else — a run that takes an
# end-to-end test still runs it exactly as it did.
def keep.solo(+want: Bool, +is_unit: Bool) -> Bool:
  Bool.and(want, Bool.not(is_unit))

# the end-to-end tests, or none of them
def solos(ts: List<&2, String>, +want: Bool) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = solos(t, want)
      Bool.pick(List<&2, String>, keep.solo(want, unit(h)), h <> more, more)

# a project named once more, or not again. The walk runs over a sorted list, so
# every test of a project is consecutive and the head of what came back is the
# only one this could repeat.
def projs.put(+d: String, +ds: List<&2, String>) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.eq(d, head.of(ds)), ds, d <> ds)

# every project that has unit tests, each named once, in the walk's order
def projs(ts: List<&2, String>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      projs.put(G.proj(h), projs(t))

# the tests of one project
def in_proj(ts: List<&2, String>, +d: String) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = in_proj(t, d)
      Bool.pick(List<&2, String>, String.eq(G.proj(h), d), h <> more, more)

# the tests of a project that the JS lane takes, which is every one whose
# header does not hand it to the native lane alone. The header is in the file,
# so this reads them.
def js_of(ts: List<&2, String>) -> IO(List<&2, String>):
  match ts:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case Con{+h, t}:
      do IO<List<&2, String>>:
        src : Maybe<&2, String> <- F.read(h)
        +more : List<&2, String> <- js_of(t)
        return Bool.pick(List<&2, String>, js_lane(F.text_of(src)), h <> more, more)

# what is being worked on, while it is worked on, so a run that takes minutes
# says so. Off unless EZ_PROGRESS asks, because the one thing reading a run is
# entitled to expect is that its last line is the count: the effect hands back
# stdout and stderr down one pipe, so whichever is flushed last wins, and a
# progress line must not be able to win.
def saying(on: Bool, +what: String) -> IO(Unit):
  match on:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      IO.print_err("  " ++ what)

# whether a run says what it is doing as it does it
def progress() -> IO(Bool):
  do IO<Bool>:
    +v : String <- Env.var("EZ_PROGRESS", "")
    return Bool.not(String.is_empty(v))

# a test the JS lane will not take, named. A lane that drops a file says so
# out loud: the count alone cannot tell a run of every test from a run of
# fewer, and the header that dropped it is a line in a file someone wrote by
# hand and may have written by accident.
def dropped(taken: Bool, +path: String) -> IO(Unit):
  match taken:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print("skip: " ++ path ++ " (js): its header hands it to the " ++
        "native lane alone")

# every test of a project the JS lane will not take
def drops(ts: List<&2, String>, +js: List<&2, String>) -> IO(Unit):
  match ts:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, t}:
      do IO<Unit>:
        dropped(G.holds(js, h), h)
        drops(t, js)

# a project's tests as one program, written into the project's place in the
# shadow. The shadow makes the project's directory; the one the aggregates
# themselves sit in is theirs and is made here.
def made(+dir: String, +name: String, +ts: List<&2, String>) -> IO(Bool):
  do IO<Bool>:
    _mk : String <- R.exec(["mkdir", "-p", G.agg.at(dir)])
    F.write(G.src(dir, name), G.agg(dir, ts))

# what a test observed: its slice of the run, or the reason it could not have
# one. Tests in an aggregate share a process and so share its command line, so
# a test that reads `IO.args()` is answered with that rather than with output
# it could not have produced. No test in this repo reads it; the environment,
# which some do read, is the same either way.
def observed(alone: Bool, +text: String, +path: String) -> String:
  Bool.pick(String, alone,
    "this test reads IO.args(), and every test of a project shares one binary",
    Q.chomp(G.slice(text, path)))

# one test against its own slice of the run its project shared
def section(+path: String, +lane: String, +text: String, t: Tally) -> IO(Tally):
  do IO<Tally>:
    src : Maybe<&2, String> <- F.read(path)
    +body : String <- IO.pure(String, F.text_of(src))
    check(path ++ " (" ++ lane ++ ")", G.trailer(body),
      observed(G.solitary(body), text, path), t)

# every test of a project, each against its own slice
def sections(ts: List<&2, String>, +lane: String, +text: String,
  t: Tally) -> IO(Tally):
  match ts:
    case Nil{}:
      IO.pure(Tally, t)
    case Con{+h, rest}:
      do IO<Tally>:
        next : Tally <- section(h, lane, text, t)
        sections(rest, lane, text, next)

# one test that never ran, because the binary holding it did not
def miss(+path: String, +lane: String, +why: String, t: Tally) -> IO(Tally):
  do IO<Tally>:
    src : Maybe<&2, String> <- F.read(path)
    check(path ++ " (" ++ lane ++ ")", G.trailer(F.text_of(src)), why, t)

# every test of a project that never ran. They are failed one by one rather
# than skipped: a project whose binary will not build has answered for nothing.
def missed(ts: List<&2, String>, +lane: String, +why: String,
  t: Tally) -> IO(Tally):
  match ts:
    case Nil{}:
      IO.pure(Tally, t)
    case Con{+h, rest}:
      do IO<Tally>:
        next : Tally <- miss(h, lane, why, t)
        missed(rest, lane, why, next)

# what each test of a project is told when the one binary did not run
def unran(+dir: String) -> String:
  "(" ++ dir ++ "'s one binary did not build or did not start)"

# the project named, and whatever its build or its run said, printed once
# rather than once a test. A build killed at the memory cap says so here.
def blame(+dir: String, +lane: String, +text: String) -> IO(Unit):
  IO.write("FAIL: " ++ dir ++ " (" ++ lane ++ "): the one binary did not " ++
    "build or did not start, so no test of it ran\n" ++ indent(text))

# an aggregate's output handed to the tests it holds, or a failure that names
# the project. A test that runs as a `main` can still fail to import, and then
# nothing of the project ran: the run reaching no marker at all is how that
# looks, and it is loud rather than silent.
def answer(ok: Bool, ts: List<&2, String>, +dir: String, +lane: String,
  +text: String, t: Tally) -> IO(Tally):
  match ok:
    case True{}:
      sections(ts, lane, text, t)
    case False{}:
      do IO<Tally>:
        blame(dir, lane, text)
        missed(ts, lane, unran(dir), t)

# how many comparisons did not hold
def flops(t: Tally) -> Nat:
  Tally{p, n} = t
  Nat.sub(n, p)

# a lane's answer remembered, and only when every test of it held. A cache that
# went green on stale evidence would be worse than no cache at all, so nothing
# is written for a lane that failed, and `--full` reads none of it.
def remember(+before: Tally, +after: Tally, +k: String, +what: String) -> IO(Tally):
  do IO<Tally>:
    C.keep(Nat.is_eq(flops(before), flops(after)), k, what)
    return after

# a lane's tests counted without being run, because this exact evidence — every
# test, everything they import, the bodies beside those, and the toolchain —
# has already held
def hit(ts: List<&2, String>, t: Tally) -> Tally:
  match ts:
    case Nil{}:
      t
    case Con{_h, rest}:
      hit(rest, tally(True{}, t))

# ---------------------------------------------------------------------------
# One thing the gate has to run, and what its answer will mean.
#
# A lane is a project's tests in one binary, on the JS side or the native one.
# A solo is an end-to-end test: it drives git, nix and bend itself, so it wants
# a process, a scratch directory and a port of its own. A proof is a file whose
# first line is its whole verdict.
#
# Every one of them is independent of every other — the shadow gives each
# project its own directory, `check/world.bend` gives each solo its own
# `mktemp -d` and a port off bind(0), and the cache gives each lane its own key
# — so there is no shared thing to write and nothing to serialize. What there
# was instead was a runner that started them one at a time, which is why this
# list exists: gather the whole run's work first, hand it to `R.par` at once,
# then walk the answers back in the order the tree gives.
#
# A unit that has already held over exactly this evidence is `hot`. It keeps
# its place in the list rather than being filtered out, so the report still
# walks one order and no filtered list ever has to be matched back up against
# the list it came from. What a hot unit runs is a program that does nothing.
type Work is Data:
  Work.lane{hot: Bool, native: Bool, dir: String, ts: List<&2, String>, key: String}
  Work.solo{path: String}
  Work.proof{hot: Bool, path: String, key: String}

# whether a lane has any test to run at all
def any(ts: List<&2, String>) -> Bool:
  Bool.not(List.is_empty(&2, String, ts))

# a program that does nothing, for a unit with nothing to run
def idle() -> List<&2, String>:
  ["true"]

# a `bend` the runner starts: inside the memory cap, inside the budget, and
# with this project's BEND_LIB set for it
def under(cap: Bool, +g: String, +at: String,
  args: List<&2, String>) -> List<&2, String>:
  Cap.argv(cap, g, at, args)

# what running a lane means: the aggregate compiled to a binary, or the
# aggregate interpreted where it stands
def lane.cmd(native: Bool, +dir: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, native,
    ["bend", G.src(dir, "all"), "-o", G.bin(dir)],
    ["bend", G.src(dir, "all.js")])

# the program a unit runs first, before anything about it is known
def first(w: Work, cap: Bool, +g: String, +at: String) -> List<&2, String>:
  match w:
    case Work.lane{hot, native, +dir, _ts, _key}:
      Bool.pick(List<&2, String>, hot, idle(),
        under(cap, g, at, lane.cmd(native, dir)))
    case Work.solo{+path}:
      under(cap, g, at, ["bend", path])
    case Work.proof{hot, +path, _key}:
      Bool.pick(List<&2, String>, hot, idle(), under(cap, g, at, ["bend", path]))

# the program a unit runs once the first one is done. Only a native lane has
# one, and it is the binary the first program wrote. Every other unit answers
# with the program that does nothing, so the two lists stay exactly as long as
# the work list and the report can walk all three together.
#
# A lane whose compile failed has no binary and this answers 127 for it, which
# costs nothing and is never read: the report branches on the compile's own
# status. Nor can it find a binary left over from a run before, because the
# shadow the binaries live in is built from nothing every time.
def second(w: Work) -> List<&2, String>:
  match w:
    case Work.lane{hot, native, +dir, _ts, _key}:
      Bool.pick(List<&2, String>, Bool.and(native, Bool.not(hot)),
        [G.bin(dir), "--gpu", "off"], idle())
    case Work.solo{_path}:
      idle()
    case Work.proof{_hot, _path, _key}:
      idle()

# every unit's first program, in the work list's order
def firsts(ws: List<&2, Work>, +cap: Bool, +g: String, +at: String) -> List<&2, List<&2, String>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      first(h, cap, g, at) <> firsts(t, cap, g, at)

# every unit's second program, in the same order
def seconds(ws: List<&2, Work>) -> List<&2, List<&2, String>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      second(h) <> seconds(t)

# ---------------------------------------------------------------------------
# Planning: what the run will do, decided before any of it is started.

# a project's two lanes: the aggregates written, the keys taken, and each lane
# asked whether it has already held over exactly this evidence
def plan.lanes(js_on: Bool, native_on: Bool, hj: Bool, hn: Bool, +dir: String,
  jts: List<&2, String>, ts: List<&2, String>, +kj: String,
  +kn: String) -> List<&2, Work>:
  List.append(&2, Work,
    Bool.pick(List<&2, Work>, js_on, [Work.lane{hj, False{}, dir, jts, kj}], []),
    Bool.pick(List<&2, Work>, native_on, [Work.lane{hn, True{}, dir, ts, kn}], []))

# one project planned, on both lanes
def plan.project(+dir: String, +ts: List<&2, String>, +on: Bool, +full: Bool,
  +tool: String, +loud: Bool) -> IO(List<&2, Work>):
  do IO<List<&2, Work>>:
    saying(loud, dir)
    +jts : List<&2, String> <- js_of(ts)
    drops(ts, jts)
    _wj : Bool <- made(dir, "all.js", jts)
    _wn : Bool <- made(dir, "all", ts)
    +kj : String <- C.key.on(any(jts), "js", tool, G.src(dir, "all.js"))
    +kn : String <- C.key.on(on, "cpu", tool, G.src(dir, "all"))
    +hj : Bool <- C.fresh(Bool.not(full), kj)
    +hn : Bool <- C.fresh(Bool.not(full), kn)
    return plan.lanes(any(jts), on, hj, hn, dir, jts, ts, kj, kn)

# every project with unit tests, in order
def plan.projects(ds: List<&2, String>, +ts: List<&2, String>, +on: Bool,
  +full: Bool, +tool: String, +loud: Bool) -> IO(List<&2, Work>):
  match ds:
    case Nil{}:
      IO.pure(List<&2, Work>, Nil{})
    case Con{+h, rest}:
      do IO<List<&2, Work>>:
        here : List<&2, Work> <- plan.project(h, in_proj(ts, h), on, full, tool, loud)
        more : List<&2, Work> <- plan.projects(rest, ts, on, full, tool, loud)
        return List.append(&2, Work, here, more)

# every end-to-end test. These are never cached: what they read is the world
# outside this repo, and no key made of file contents says whether that
# changed.
def plan.solos(es: List<&2, String>, +loud: Bool) -> IO(List<&2, Work>):
  match es:
    case Nil{}:
      IO.pure(List<&2, Work>, Nil{})
    case Con{+h, rest}:
      do IO<List<&2, Work>>:
        saying(loud, h)
        more : List<&2, Work> <- plan.solos(rest, loud)
        return Work.solo{h} <> more

# one proof, keyed on what it reads. A proof reads its own closure and nothing
# else, so it keys the way a lane does.
def plan.proof(+path: String, +full: Bool, +tool: String,
  +loud: Bool) -> IO(Work):
  do IO<Work>:
    saying(loud, path)
    +k : String <- C.key("proof", tool, path)
    +hot : Bool <- C.fresh(Bool.not(full), k)
    return Work.proof{hot, path, k}

# every proof in the tree
def plan.proofs(ps: List<&2, String>, +full: Bool, +tool: String,
  +loud: Bool) -> IO(List<&2, Work>):
  match ps:
    case Nil{}:
      IO.pure(List<&2, Work>, Nil{})
    case Con{+h, rest}:
      do IO<List<&2, Work>>:
        w : Work <- plan.proof(h, full, tool, loud)
        more : List<&2, Work> <- plan.proofs(rest, full, tool, loud)
        return w <> more

# the whole run's work, in the order the report will walk it
def plan(ds: List<&2, String>, +us: List<&2, String>, es: List<&2, String>,
  ps: List<&2, String>, +on: Bool, +full: Bool, +tool: String,
  +loud: Bool) -> IO(List<&2, Work>):
  do IO<List<&2, Work>>:
    ls : List<&2, Work> <- plan.projects(ds, us, on, full, tool, loud)
    ss : List<&2, Work> <- plan.solos(es, loud)
    qs : List<&2, Work> <- plan.proofs(ps, full, tool, loud)
    return List.append(&2, Work, ls, List.append(&2, Work, ss, qs))

# ---------------------------------------------------------------------------
# Reporting: each unit against its own answer, in the tree's order.

# the JS lane's answer: the run's output, with a memory kill turned into a
# sentence in front of it
def report.js(+dir: String, ts: List<&2, String>, +key: String, +g: String,
  +a: String, +t: Tally) -> IO(Tally):
  do IO<Tally>:
    +text : String <- IO.pure(String, Cap.why(a, g) ++ Q.filter(R.text(a)))
    after : Tally <- answer(G.started(text), ts, dir, "js", text, t)
    remember(t, after, key, dir ++ " (js)")

# the native lane once its binary is either built or not. A build that failed
# is itself the failure, and its output is what is reported.
def report.cpu(ok: Bool, +dir: String, ts: List<&2, String>, +key: String,
  +why: String, +a: String, +t: Tally) -> IO(Tally):
  match ok:
    case False{}:
      do IO<Tally>:
        blame(dir, "cpu", why)
        missed(ts, "cpu", unran(dir), t)
    case True{}:
      do IO<Tally>:
        +text : String <- IO.pure(String, Q.chomp(R.text(a)))
        after : Tally <- answer(G.started(text), ts, dir, "cpu", text, t)
        remember(t, after, key, dir ++ " (cpu)")

# a lane that ran, on whichever side it was
def report.lane(native: Bool, +dir: String, ts: List<&2, String>, +key: String,
  +g: String, +a1: String, +a2: String, t: Tally) -> IO(Tally):
  match native:
    case False{}:
      report.js(dir, ts, key, g, a1, t)
    case True{}:
      report.cpu(R.ok(a1), dir, ts, key,
        Cap.why(a1, g) ++ Q.filter(R.text(a1)), a2, t)

# a lane, unless it has already held, in which case its tests are counted
# without being run
def report.hot(hot: Bool, native: Bool, +dir: String, ts: List<&2, String>,
  +key: String, +g: String, +a1: String, +a2: String, t: Tally) -> IO(Tally):
  match hot:
    case True{}:
      IO.pure(Tally, hit(ts, t))
    case False{}:
      report.lane(native, dir, ts, key, g, a1, a2, t)

# one end-to-end test against its own trailer
def report.solo(+path: String, +a: String, t: Tally) -> IO(Tally):
  do IO<Tally>:
    src : Maybe<&2, String> <- F.read(path)
    check(path ++ " (js)", G.trailer(F.text_of(src)), Q.filter(R.text(a)), t)

# a proof's verdict is the line, never the exit status. Both
# `All terms check, with N unsafe annotations.` and 2.0.18's
# `All terms check, but N defs rely on unsafe or foreign code:` exit 0, so a
# gate reading the status alone goes green on a claim that leans on code
# nothing proved. Only the bare line means every term was proved outright.
def report.proof(hot: Bool, +path: String, +key: String, +a: String,
  +t: Tally) -> IO(Tally):
  match hot:
    case True{}:
      IO.pure(Tally, tally(True{}, t))
    case False{}:
      do IO<Tally>:
        after : Tally <- check(path, "All terms check.", head(R.text(a)), t)
        remember(t, after, key, path)

# one unit against the two answers its place in the order gave it
def report.one(w: Work, +g: String, +a1: String, +a2: String,
  t: Tally) -> IO(Tally):
  match w:
    case Work.lane{hot, native, +dir, ts, +key}:
      report.hot(hot, native, dir, ts, key, g, a1, a2, t)
    case Work.solo{+path}:
      report.solo(path, a1, t)
    case Work.proof{hot, +path, +key}:
      report.proof(hot, path, key, a1, t)

# every unit the answers ran out before. The three lists are the same length by
# construction and this should never have one to report, but the alternative to
# saying so is a green count over fewer tests than the tree holds, which is the
# worst answer a gate can give.
def report.short(ws: List<&2, Work>, t: Tally) -> IO(Tally):
  match ws:
    case Nil{}:
      IO.pure(Tally, t)
    case Con{_h, rest}:
      do IO<Tally>:
        IO.write("FAIL: the run planned a unit it never got an answer for\n")
        report.short(rest, tally(False{}, t))

# every unit, in the tree's order however the run happened to interleave. The
# three lists are the same length by construction, so they are walked as one.
def report(ws: List<&2, Work>, a1: List<&2, String>, a2: List<&2, String>,
  +g: String, t: Tally) -> IO(Tally):
  match ws a1 a2:
    case Con{h, wt} Con{+x, xt} Con{+y, yt}:
      do IO<Tally>:
        next : Tally <- report.one(h, g, x, y, t)
        report(wt, xt, yt, g, next)
    case rest _x _y:
      report.short(rest, t)

# every file of a kind in the tree, sorted, so a run's report is the same twice
# over. Base has no readdir, so this is `find`. `.claude` is skipped along with
# `.ez`: an agent's worktree is a whole second copy of the repo living inside
# it, and running its tests would double the gate to test nothing new.
#
# Skipping `.ez` is also what keeps the shadow from being walked. Every test
# stands in it a second time, under a symlink, and a gate that counted both
# would double itself and learn nothing; `find` does not follow symlinks
# unless asked, and `./.ez/*` rules out the shadow's own paths besides.
def find.at(+what: String, +how: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    out : String <- R.exec(["find", ".", how, what,
      "-not", "-path", "./.ez/*",
      "-not", "-path", "./.git/*", "-not", "-path", "./.claude/*"])
    return Sort.sort(Args.nonempty(String.lines(R.text(out))))

# where the repo is, absolutely. The shadow's links point at it: a relative
# target would have to count the levels of the link that carries it, and an
# absolute one reads the same from every depth of the shadow.
def here() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["pwd"])
    return String.trim(R.text(out))

# what one directory of the repo holds, one level down. `.ez` is left out
# because the shadow lives there and must not stand inside itself, `.git` and
# `.claude` because no import ever reaches through them.
def entries(+dir: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    out : String <- R.exec(["find", G.of(dir), "-mindepth", "1", "-maxdepth", "1",
      "-not", "-name", ".ez", "-not", "-name", ".git", "-not", "-name", ".claude"])
    return Sort.sort(Args.nonempty(String.lines(R.text(out))))

# the paths as the shadow's links have to name them
def abs(+repo: String, es: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      (repo ++ "/" ++ G.rel(h)) <> abs(repo, t)

# a link in one shadow directory to each of these, under the name the repo
# gives it. `ln` takes them all at once, so a level costs one program run
# however wide it is, and an empty level costs none.
def link(+repo: String, +at: String, es: List<&2, String>) -> IO(Unit):
  match es:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{h, t}:
      do IO<Unit>:
        _o : String <- R.exec(List.append(&2, String, ["ln", "-s"],
          List.append(&2, String, abs(repo, h <> t), [at])))
        return Unit{}

# one level of the shadow: the directory made, and a link in it to every entry
# of the real directory that no project needs carved out of it
def level(+repo: String, +dir: String, ds: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", G.at(dir)])
    es : List<&2, String> <- entries(dir)
    link(repo, G.at(dir), G.linked(es, ds))

# every level, in order
def levels(ls: List<&2, String>, +repo: String, +ds: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, t}:
      do IO<Unit>:
        level(repo, h, ds)
        levels(t, repo, ds)

# the shadow the aggregates are compiled in, built from nothing so that a file
# deleted since the last run leaves no link behind
def shadow(+repo: String, +ds: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", G.root()])
    levels(G.levels(ds), repo, ds)

# every test file
def find() -> IO(List<&2, String>):
  find.at("*/tests/*.bend", "-path")

# every proof file
def find.proofs() -> IO(List<&2, String>):
  find.at("PROOF.bend", "-name")

# anything that failed fails the command, or a script around it learns nothing
def done.exit(all: Bool) -> IO(Unit):
  match all:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "")

# the count, and the exit status it implies. The reminder sits above the count
# and never below it: a run's last line is its verdict, and something reads it.
def done.go(+p: Nat, +n: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.print("tests are a last resort for what you cannot prove")
    IO.print("PASS: " ++ Nat.show(p) ++ " / " ++ Nat.show(n))
    done.exit(Nat.is_eq(p, n))

# what a whole run amounts to
def done(t: Tally) -> IO(Unit):
  Tally{p, n} = t
  done.go(p, n)

# where the jobs of a run write what they print. One directory a wave, made
# fresh, so nothing a run reads was written by the run before it.
def out.at(+wave: String) -> String:
  ".ez/run/" ++ wave

# how many `bend` runs may be in flight at once. Empty is the usual answer and
# means the effect works it out: cores, but never more of them than the memory
# cap divides the machine into, since each one of these may claim the whole
# cap. EZ_JOBS overrides it for a machine that knows better.
def width() -> IO(String):
  Env.var("EZ_JOBS", "")

# the budget checked the way every other thing here is checked. A run that
# overran is a run that failed, and it says so in the count rather than merely
# taking a long time.
def budget(late: Bool, +s: String, t: Tally) -> IO(Tally):
  match late:
    case False{}:
      IO.pure(Tally, t)
    case True{}:
      do IO<Tally>:
        IO.write("FAIL: the gate took longer than its " ++ s ++ " second " ++
          "budget\n  set EZ_DEADLINE higher if this tree honestly needs " ++
          "longer, or to 0 to stop asking\n")
        return tally(False{}, t)

# a directory emptied and made again
def fresh.dir(+at: String) -> IO(Unit):
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", at])
    _mk : String <- R.exec(["mkdir", "-p", at])
    return Unit{}

# `ez test [--js-only] [--full] [--unit-only]`: every test in the tree, on
# every lane.
#
# The whole run is planned before any of it is started, then handed to `R.par`
# in two waves: what every unit runs first, and then the binaries the native
# lanes just built. Nothing here is ordered against anything else — a project
# has its own directory in the shadow, an end-to-end test its own scratch
# directory and port, a lane its own cache key — so the only thing the old
# one-at-a-time runner bought was the order of the report, and the report is
# still walked in the tree's order whatever order the jobs finished in.
def run(+js_only: Bool, +full: Bool, +unit_only: Bool) -> IO(Unit):
  do IO<Unit>:
    C.make()
    +repo : String <- here()
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +loud : Bool <- progress()
    +tool : String <- C.tool()
    +secs : String <- Clock.seconds()
    +deadline : String <- Clock.start(secs)

    +on : Bool <- IO.pure(Bool, Bool.not(js_only))
    +e2e : Bool <- IO.pure(Bool, Bool.not(unit_only))
    +g : String <- Cap.gb()
    +at : String <- Env.lib()
    +jobs : String <- width()
    +ts : List<&2, String> <- find()
    +us : List<&2, String> <- IO.pure(List<&2, String>, some(ts, True{}))
    es : List<&2, String> <- IO.pure(List<&2, String>, solos(ts, e2e))
    shadow(repo, projs(us))
    ps : List<&2, String> <- find.proofs()
    +ws : List<&2, Work> <- plan(projs(us), us, es, ps, on, full, tool, loud)
    fresh.dir(out.at("1"))
    fresh.dir(out.at("2"))
    +by : String <- IO.pure(String, Clock.by.effect(deadline))
    a1 : List<&2, String> <- R.par(firsts(ws, cap, g, at), jobs, g, out.at("1"), by)
    a2 : List<&2, String> <- R.par(seconds(ws), jobs, g, out.at("2"), by)
    every : Tally <- report(ws, a1, a2, g, Tally{0n, 0n})
    +late : Bool <- Clock.over(deadline)
    kept : Tally <- budget(late, secs, every)
    done(kept)

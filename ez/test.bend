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
# answers for its own trailer.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ./args.bend as Args
import ./env.bend as Env
import ./cap.bend as Cap
import ./gate.bend as G
import ./quiet.bend as Q

# how many comparisons were made, and how many of them held
type Tally is Data:
  Tally{pass: Nat, total: Nat}

# a trailer line kept, with its `#|` dropped, or a source line ignored
def want.put(is_want: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match is_want:
    case True{}:
      String.drop(h, 2n) <> rest
    case False{}:
      rest

# the `#|` lines of a source file, in order
def want(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case +h <> t:
      want.put(String.starts_with(h, "#|"), h, want(t))

# what a test file says its run must print
def trailer(text: String) -> String:
  String.join(want(String.lines(text)), "\n")

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
def js_lane(+text: String) -> Bool:
  Bool.not(String.contains(text, "# lanes: native"))

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

# a project's tests as one program, written beside them
def made(+dir: String, +name: String, +ts: List<&2, String>) -> IO(Bool):
  do IO<Bool>:
    _mk : String <- R.exec(["mkdir", "-p", G.at(dir)])
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
    check(path ++ " (" ++ lane ++ ")", trailer(body),
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
    check(path ++ " (" ++ lane ++ ")", trailer(F.text_of(src)), why, t)

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

# the JS lane: one `bend` over the project's aggregate, interpreted
def js(cap: Bool, +dir: String, ts: List<&2, String>, t: Tally) -> IO(Tally):
  do IO<Tally>:
    +g : String <- Cap.gb()
    +out : String <- Cap.run(cap, ["bend", G.src(dir, "all.js")])
    +text : String <- IO.pure(String, Cap.why(out, g) ++ Q.filter(R.text(out)))
    answer(G.started(text), ts, dir, "js", text, t)

# the native lane, once the project's binary is either built or not. A build
# that failed is itself the failure, and its output is what is reported.
def built(ok: Bool, +why: String, +dir: String, ts: List<&2, String>,
  t: Tally) -> IO(Tally):
  match ok:
    case False{}:
      do IO<Tally>:
        blame(dir, "cpu", why)
        missed(ts, "cpu", unran(dir), t)
    case True{}:
      do IO<Tally>:
        out : String <- R.exec([G.bin(dir), "--gpu", "off"])
        +text : String <- IO.pure(String, Q.chomp(R.text(out)))
        answer(G.started(text), ts, dir, "cpu", text, t)

# the native CPU lane: the project compiled once, then the binary run. An
# aggregate is a larger compile than any one of its tests, so this is where the
# cap bites first; `Cap.why` turns the kernel's 137 into a sentence, because
# bend prints that all terms check before it emits any C.
def cpu(on: Bool, cap: Bool, +dir: String, ts: List<&2, String>,
  t: Tally) -> IO(Tally):
  match on:
    case False{}:
      IO.pure(Tally, t)
    case True{}:
      do IO<Tally>:
        +g : String <- Cap.gb()
        +out : String <- Cap.run(cap, ["bend", G.src(dir, "all"), "-o", G.bin(dir)])
        built(R.ok(out), Cap.why(out, g) ++ Q.filter(R.text(out)), dir, ts, t)

# whether a lane has any test to run at all
def any(ts: List<&2, String>) -> Bool:
  Bool.not(List.is_empty(&2, String, ts))

# the JS lane of a project, unless every test of it is native-only
def js.on(on: Bool, cap: Bool, +dir: String, ts: List<&2, String>,
  t: Tally) -> IO(Tally):
  match on:
    case False{}:
      IO.pure(Tally, t)
    case True{}:
      js(cap, dir, ts, t)

# one project, on both lanes, one `bend` each
def project(+dir: String, +ts: List<&2, String>, +cap: Bool, +on: Bool,
  +loud: Bool, t: Tally) -> IO(Tally):
  do IO<Tally>:
    saying(loud, dir)
    +jts : List<&2, String> <- js_of(ts)
    _wj : Bool <- made(dir, "all.js", jts)
    _wn : Bool <- made(dir, "all", ts)
    first : Tally <- js.on(any(jts), cap, dir, jts, t)
    cpu(on, cap, dir, ts, first)

# every project with unit tests, in order
def projects(ds: List<&2, String>, +ts: List<&2, String>, +cap: Bool,
  +on: Bool, +loud: Bool, t: Tally) -> IO(Tally):
  match ds:
    case Nil{}:
      IO.pure(Tally, t)
    case Con{+h, rest}:
      do IO<Tally>:
        next : Tally <- project(h, in_proj(ts, h), cap, on, loud, t)
        projects(rest, ts, cap, on, loud, next)

# one end-to-end test, on the JS lane alone. These drive git, nix and bend
# itself, so each one is its own process and its own `bend`.
def one(+path: String, cap: Bool, loud: Bool, t: Tally) -> IO(Tally):
  do IO<Tally>:
    saying(loud, path)
    src : Maybe<&2, String> <- F.read(path)
    +text : String <- IO.pure(String, F.text_of(src))
    out : String <- Cap.run(cap, ["bend", path])
    check(path ++ " (js)", trailer(text), Q.filter(R.text(out)), t)

# every end-to-end test, in order. The list comes first because a self-call
# must shrink an argument before it changes one.
def each(ts: List<&2, String>, +cap: Bool, +loud: Bool, t: Tally) -> IO(Tally):
  match ts:
    case []:
      IO.pure(Tally, t)
    case h <> rest:
      do IO<Tally>:
        next : Tally <- one(h, cap, loud, t)
        each(rest, cap, loud, next)

# a proof's verdict is the line, never the exit status. Both
# `All terms check, with N unsafe annotations.` and 2.0.18's
# `All terms check, but N defs rely on unsafe or foreign code:` exit 0, so a
# gate reading the status alone goes green on a claim that leans on code
# nothing proved. Only the bare line means every term was proved outright.
def proof(+path: String, cap: Bool, loud: Bool, t: Tally) -> IO(Tally):
  do IO<Tally>:
    saying(loud, path)
    +out : String <- Cap.run(cap, ["bend", path])
    check(path, "All terms check.", head(R.text(out)), t)

# every proof in the tree, checked
def proofs(ps: List<&2, String>, +cap: Bool, +loud: Bool, t: Tally) -> IO(Tally):
  match ps:
    case []:
      IO.pure(Tally, t)
    case h <> rest:
      do IO<Tally>:
        next : Tally <- proof(h, cap, loud, t)
        proofs(rest, cap, loud, next)

# every file of a kind in the tree, sorted, so a run's report is the same twice
# over. Base has no readdir, so this is `find`. `.claude` is skipped along with
# the build directories: an agent's worktree is a whole second copy of the repo
# living inside it, and running its tests would double the gate to test nothing
# new. A `.gate` is skipped wherever it is, since that is where the aggregates
# this runner writes for itself land.
def find.at(+what: String, +how: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    out : String <- R.exec(["find", ".", how, what,
      "-not", "-path", "./.ez/*", "-not", "-path", "*/.gate/*",
      "-not", "-path", "./.git/*", "-not", "-path", "./.claude/*"])
    return List.sort(~String, ~String.is_le, Args.nonempty(String.lines(R.text(out))))

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

# `ez test [--js-only]`: every test in the tree, on every lane
def run(as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", ".gate"])
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +loud : Bool <- progress()
    +ts : List<&2, String> <- find()
    +us : List<&2, String> <- IO.pure(List<&2, String>, some(ts, True{}))
    es : List<&2, String> <- IO.pure(List<&2, String>, some(ts, False{}))
    t : Tally <- projects(projs(us), us, cap,
      Bool.not(String.eq(Args.at(as, 0n), "--js-only")), loud, Tally{0n, 0n})
    e : Tally <- each(es, cap, loud, t)
    ps : List<&2, String> <- find.proofs()
    every : Tally <- proofs(ps, cap, loud, e)
    done(every)

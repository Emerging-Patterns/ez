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

# the JS lane: one `bend` over the project's aggregate, interpreted
def js.run(cap: Bool, +dir: String, ts: List<&2, String>, +k: String,
  +t: Tally) -> IO(Tally):
  do IO<Tally>:
    +g : String <- Cap.gb()
    +out : String <- Cap.run(cap, ["bend", G.src(dir, "all.js")])
    +text : String <- IO.pure(String, Cap.why(out, g) ++ Q.filter(R.text(out)))
    after : Tally <- answer(G.started(text), ts, dir, "js", text, t)
    remember(t, after, k, dir ++ " (js)")

# the JS lane, unless it has already held over this same evidence
def js(hot: Bool, cap: Bool, +dir: String, ts: List<&2, String>, +k: String,
  +t: Tally) -> IO(Tally):
  match hot:
    case True{}:
      IO.pure(Tally, hit(ts, t))
    case False{}:
      js.run(cap, dir, ts, k, t)

# the native lane, once the project's binary is either built or not. A build
# that failed is itself the failure, and its output is what is reported.
def built(ok: Bool, +why: String, +dir: String, ts: List<&2, String>,
  +k: String, +t: Tally) -> IO(Tally):
  match ok:
    case False{}:
      do IO<Tally>:
        blame(dir, "cpu", why)
        missed(ts, "cpu", unran(dir), t)
    case True{}:
      do IO<Tally>:
        out : String <- R.exec([G.bin(dir), "--gpu", "off"])
        +text : String <- IO.pure(String, Q.chomp(R.text(out)))
        after : Tally <- answer(G.started(text), ts, dir, "cpu", text, t)
        remember(t, after, k, dir ++ " (cpu)")

# the native CPU lane: the project compiled once, then the binary run. An
# aggregate is a larger compile than any one of its tests, so this is where the
# cap bites first; `Cap.why` turns the kernel's 137 into a sentence, because
# bend prints that all terms check before it emits any C.
def cpu.run(cap: Bool, +dir: String, ts: List<&2, String>, +k: String,
  t: Tally) -> IO(Tally):
  do IO<Tally>:
    +g : String <- Cap.gb()
    +out : String <- Cap.run(cap, ["bend", G.src(dir, "all"), "-o", G.bin(dir)])
    built(R.ok(out), Cap.why(out, g) ++ Q.filter(R.text(out)), dir, ts, k, t)

# the native lane, unless `--js-only` turned it off or it has already held over
# this same evidence
def cpu.hot(hot: Bool, cap: Bool, +dir: String, ts: List<&2, String>,
  +k: String, +t: Tally) -> IO(Tally):
  match hot:
    case True{}:
      IO.pure(Tally, hit(ts, t))
    case False{}:
      cpu.run(cap, dir, ts, k, t)

# the native lane, unless `--js-only` turned it off
def cpu(on: Bool, hot: Bool, cap: Bool, +dir: String, ts: List<&2, String>,
  +k: String, t: Tally) -> IO(Tally):
  match on:
    case False{}:
      IO.pure(Tally, t)
    case True{}:
      cpu.hot(hot, cap, dir, ts, k, t)

# whether a lane has any test to run at all
def any(ts: List<&2, String>) -> Bool:
  Bool.not(List.is_empty(&2, String, ts))

# the JS lane of a project, unless every test of it is native-only
def js.on(on: Bool, hot: Bool, cap: Bool, +dir: String, ts: List<&2, String>,
  +k: String, t: Tally) -> IO(Tally):
  match on:
    case False{}:
      IO.pure(Tally, t)
    case True{}:
      js(hot, cap, dir, ts, k, t)

# one project, on both lanes, one `bend` each — and neither of them at all when
# nothing either lane reads has changed since it last held
def project(+dir: String, +ts: List<&2, String>, +cap: Bool, +on: Bool,
  +full: Bool, +tool: String, +loud: Bool, t: Tally) -> IO(Tally):
  do IO<Tally>:
    saying(loud, dir)
    +jts : List<&2, String> <- js_of(ts)
    drops(ts, jts)
    _wj : Bool <- made(dir, "all.js", jts)
    _wn : Bool <- made(dir, "all", ts)
    +kj : String <- C.key.on(any(jts), "js", tool, G.src(dir, "all.js"))
    +kn : String <- C.key.on(on, "cpu", tool, G.src(dir, "all"))
    +hj : Bool <- C.fresh(Bool.not(full), kj)
    +hn : Bool <- C.fresh(Bool.not(full), kn)
    first : Tally <- js.on(any(jts), hj, cap, dir, jts, kj, t)
    cpu(on, hn, cap, dir, ts, kn, first)

# every project with unit tests, in order
def projects(ds: List<&2, String>, +ts: List<&2, String>, +cap: Bool,
  +on: Bool, +full: Bool, +tool: String, +loud: Bool, t: Tally) -> IO(Tally):
  match ds:
    case Nil{}:
      IO.pure(Tally, t)
    case Con{+h, rest}:
      do IO<Tally>:
        next : Tally <- project(h, in_proj(ts, h), cap, on, full, tool, loud, t)
        projects(rest, ts, cap, on, full, tool, loud, next)

# one end-to-end test, on the JS lane alone. These drive git, nix and bend
# itself, so each one is its own process and its own `bend`.
def one(+path: String, cap: Bool, loud: Bool, t: Tally) -> IO(Tally):
  do IO<Tally>:
    saying(loud, path)
    src : Maybe<&2, String> <- F.read(path)
    +text : String <- IO.pure(String, F.text_of(src))
    out : String <- Cap.run(cap, ["bend", path])
    check(path ++ " (js)", G.trailer(text), Q.filter(R.text(out)), t)

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
def proof.run(+path: String, cap: Bool, +k: String, +t: Tally) -> IO(Tally):
  do IO<Tally>:
    +out : String <- Cap.run(cap, ["bend", path])
    after : Tally <- check(path, "All terms check.", head(R.text(out)), t)
    remember(t, after, k, path)

# a proof, unless it has already held over this same evidence. A proof reads
# its own closure and nothing else, so it keys the way a lane does.
def proof.hot(hot: Bool, +path: String, cap: Bool, +k: String,
  +t: Tally) -> IO(Tally):
  match hot:
    case True{}:
      IO.pure(Tally, tally(True{}, t))
    case False{}:
      proof.run(path, cap, k, t)

# one proof, keyed on what it reads
def proof(+path: String, cap: Bool, +full: Bool, +tool: String, loud: Bool,
  t: Tally) -> IO(Tally):
  do IO<Tally>:
    saying(loud, path)
    +k : String <- C.key("proof", tool, path)
    +hot : Bool <- C.fresh(Bool.not(full), k)
    proof.hot(hot, path, cap, k, t)

# every proof in the tree, checked
def proofs(ps: List<&2, String>, +cap: Bool, +full: Bool, +tool: String,
  +loud: Bool, t: Tally) -> IO(Tally):
  match ps:
    case []:
      IO.pure(Tally, t)
    case h <> rest:
      do IO<Tally>:
        next : Tally <- proof(h, cap, full, tool, loud, t)
        proofs(rest, cap, full, tool, loud, next)

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

# whether a flag was given, wherever among the arguments it sits
def flag(as: List<&2, String>, +name: String) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(String.eq(h, name), flag(t, name))

# `ez test [--js-only] [--full]`: every test in the tree, on every lane. The
# end-to-end tests are never cached: what they read is the world outside this
# repo, and no key made of file contents says whether that changed.
def run(+as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    C.make()
    +repo : String <- here()
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +loud : Bool <- progress()
    +tool : String <- C.tool()
    +full : Bool <- IO.pure(Bool, flag(as, "--full"))
    +on : Bool <- IO.pure(Bool, Bool.not(flag(as, "--js-only")))
    +ts : List<&2, String> <- find()
    +us : List<&2, String> <- IO.pure(List<&2, String>, some(ts, True{}))
    es : List<&2, String> <- IO.pure(List<&2, String>, some(ts, False{}))
    shadow(repo, projs(us))
    t : Tally <- projects(projs(us), us, cap, on, full, tool, loud, Tally{0n, 0n})
    e : Tally <- each(es, cap, loud, t)
    ps : List<&2, String> <- find.proofs()
    every : Tally <- proofs(ps, cap, full, tool, loud, e)
    done(every)

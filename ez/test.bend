# ez/test: the test runner. Bend has none, so a test is a `*/tests/*.bend` file
# that prints, and states in a `#|` trailer the lines its run must print. Every
# test runs twice: on the JS lane, where bend interprets it, and on the native
# CPU lane, where it is compiled to a binary first. A lane disagreeing with the
# trailer is a failure, and any failure is a non-zero exit.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ./args.bend as Args
import ./env.bend as Env
import ./cap.bend as Cap
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

# a path as `find` prints it, without the leading `./`
def rel(+path: String) -> String:
  Bool.pick(String, String.starts_with(path, "./"), String.drop(path, 2n), path)

# a file name without its `.bend`
def stem(+n: String) -> String:
  String.take(n, Nat.sub(String.length(n), 5n))

# where a test's native binary lands. The whole path becomes the name, so two
# tests called the same in different directories cannot overwrite each other.
def bin(path: String) -> String:
  ".gate/" ++ stem(String.join(String.split(rel(path), '/'), "-"))

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

# the native lane, once the binary is either built or not. A build that failed
# is itself a failure, and its output is what the test observed.
def ran(built_ok: Bool, +built: String, +path: String, +wanted: String,
  t: Tally) -> IO(Tally):
  match built_ok:
    case False{}:
      check(path ++ " (build)", "", built, t)
    case True{}:
      do IO<Tally>:
        out : String <- R.exec([bin(path), "--gpu", "off"])
        check(path ++ " (cpu)", wanted, Q.chomp(R.text(out)), t)

# whether a test is one of the unit tests, which live in a `tests/` beside the
# code they are about. The end-to-end tests are the top-level `tests/`, and
# what they drive is git, nix and bend itself: compiling the driver a second
# time would run those tools twice over to learn nothing new about them.
def unit(+path: String) -> Bool:
  Bool.not(String.starts_with(rel(path), "tests/"))

# the native CPU lane: the test compiled, then the binary run. Skipped when
# `--js-only` asked for it, since a C compile per test dominates the wall clock.
def lane(cpu: Bool, cap: Bool, +path: String, +wanted: String, t: Tally) -> IO(Tally):
  match cpu:
    case False{}:
      IO.pure(Tally, t)
    case True{}:
      do IO<Tally>:
        +g : String <- Cap.gb()
        +out : String <- Cap.run(cap, ["bend", path, "-o", bin(path)])
        ran(R.ok(out), Cap.why(out, g) ++ Q.filter(R.text(out)), path, wanted, t)

# the JS lane, which a `# lanes: native` header turns off for this test
def one.js(on: Bool, cap: Bool, +path: String, +wanted: String, t: Tally) -> IO(Tally):
  match on:
    case False{}:
      IO.pure(Tally, t)
    case True{}:
      do IO<Tally>:
        js : String <- Cap.run(cap, ["bend", path])
        check(path ++ " (js)", wanted, Q.filter(R.text(js)), t)

# what is being worked on, while it is worked on, so a run that takes minutes
# says so. Off unless EZ_PROGRESS asks, because the one thing reading a run is
# entitled to expect is that its last line is the count: the effect hands back
# stdout and stderr down one pipe, so whichever is flushed last wins, and a
# progress line must not be able to win.
def saying(on: Bool, +path: String) -> IO(Unit):
  match on:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      IO.print_err("  " ++ path)

# whether a run says what it is doing as it does it
def progress() -> IO(Bool):
  do IO<Bool>:
    +v : String <- Env.var("EZ_PROGRESS", "")
    return Bool.not(String.is_empty(v))

# one test file, on the JS lane and then the native one
def one(+path: String, +cap: Bool, cpu: Bool, +loud: Bool, t: Tally) -> IO(Tally):
  do IO<Tally>:
    saying(loud, path)
    src : Maybe<&2, String> <- F.read(path)
    +text : String <- IO.pure(String, F.text_of(src))
    +wanted : String <- IO.pure(String, trailer(text))
    first : Tally <- one.js(js_lane(text), cap, path, wanted, t)
    lane(Bool.and(cpu, unit(path)), cap, path, wanted, first)

# every test file, in order. The list comes first because a self-call must
# shrink an argument before it changes one.
def each(ts: List<&2, String>, +cap: Bool, +cpu: Bool, +loud: Bool, t: Tally) -> IO(Tally):
  match ts:
    case []:
      IO.pure(Tally, t)
    case h <> rest:
      do IO<Tally>:
        next : Tally <- one(h, cap, cpu, loud, t)
        each(rest, cap, cpu, loud, next)

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
# new.
def find.at(+what: String, +how: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    out : String <- R.exec(["find", ".", how, what,
      "-not", "-path", "./.ez/*", "-not", "-path", "./.gate/*",
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

# the count, and the exit status it implies
def done.go(+p: Nat, +n: Nat) -> IO(Unit):
  do IO<Unit>:
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
    ts : List<&2, String> <- find()
    t : Tally <- each(ts, cap, Bool.not(String.eq(Args.at(as, 0n), "--js-only")), loud, Tally{0n, 0n})
    ps : List<&2, String> <- find.proofs()
    all : Tally <- proofs(ps, cap, loud, t)
    done(all)

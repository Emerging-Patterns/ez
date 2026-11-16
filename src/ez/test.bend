# ez/test: the test runner. Bend has none, so a test is a `*/tests/*.bend` file
# that prints, and states in a `#|` trailer the lines its run must print. Each
# test is its own `bend` run, since what these drive is git, nix and bend
# itself, and each wants its own process, scratch directory and port. A run
# disagreeing with its trailer is a failure, and any failure is a non-zero
# exit.
#
# Tests are not the proof gate. `ez prove` is, and nothing here runs a proof.
import Base
import snap@1.4.0.0/main.bend as R
import ../io/file.bend as F
import ../share/env.bend as Env
import ../share/cap.bend as Cap
import ./gate.bend as G
import ./quiet.bend as Q
import ./clock.bend as Clock
import ./timer.bend as Timer
import ./prove.bend as P
import ./verdict.bend as V
import ../ez/ends.bend as E
import ../lock/run.bend as Run

# a comparison that held says nothing. One that did not prints both sides in
# full: a diff is real work in Bend, and for a handful of short lines the pair
# reads better than one would.
def say(ok: Bool, name: String, want: String, got: String) -> IO(Unit):  # noqa: L001 IO driver
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.write("FAIL: " ++ name ++ "\n  expected:\n" ++ V.indent(want) ++
        "  observed:\n" ++ V.indent(got))

# what was wanted against what happened, reported and counted
def check(name: String, +wanted: String, +got: String, score: V.Tally) -> IO(V.Tally):  # noqa: L001 IO driver
  do IO<V.Tally>:
    say(String.eq(wanted, got), name, wanted, got)
    return V.tally(String.eq(wanted, got), score)

# one test against its own trailer
def one(+path: String, +output: String, score: V.Tally) -> IO(V.Tally):  # noqa: L001 IO driver
  do IO<V.Tally>:
    src : Maybe<&2, String> <- F.read(path)
    check(path, G.trailer(F.text_of(src)), Q.filter(R.text(output)), score)

# every test the answers ran out before. The two lists are the same length by
# construction and this should never have one to report, but the alternative to
# saying so is a green count over fewer tests than the tree holds, which is the
# worst answer a gate can give.
def short(ts: List<&2, String>, score: V.Tally) -> IO(V.Tally):  # noqa: L001 IO driver
  match ts:
    case Nil{}:
      IO.pure(V.Tally, score)
    case Con{_h, rest}:
      do IO<V.Tally>:
        IO.write("FAIL: the run planned a test it never got an answer for\n")
        short(rest, V.tally(False{}, score))

# every test, in the tree's order however the run happened to interleave
def report(ts: List<&2, String>, as: List<&2, String>, score: V.Tally) -> IO(V.Tally):  # noqa: L001 IO driver
  match ts as:
    case Con{+h, tt} Con{+x, xt}:
      do IO<V.Tally>:
        next : V.Tally <- one(h, x, score)
        report(tt, xt, next)
    case rest _x:
      short(rest, score)

# every test file
def find() -> IO(List<&2, String>):  # noqa: L001 IO driver
  P.find.at("*/tests/*.bend", "-path")

# the count, and the exit status it implies. The reminder sits above the count
# and never below it: a run's last line is its verdict, and something reads it.
def done.go(+passed: Nat, +total: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.print("tests are a last resort for what you cannot prove")
    IO.print("PASS: " ++ Nat.show(passed) ++ " / " ++ Nat.show(total))
    Run.end(E.counted(passed, total))

# what a whole run amounts to
def done(score: V.Tally) -> IO(Unit):  # noqa: L001 IO driver
  V.Tally{p, n} = score
  done.go(p, n)

# where the jobs of a run write what they print
def out.at() -> String:
  ".ez/run/test"

# the budget checked the way every other thing here is checked. A run that
# overran is a run that failed, and it says so in the count rather than merely
# taking a long time.
def budget(late: Bool, +secs: String, score: V.Tally) -> IO(V.Tally):  # noqa: L001 IO driver
  match late:
    case False{}:
      IO.pure(V.Tally, score)
    case True{}:
      do IO<V.Tally>:
        IO.write("FAIL: the gate took longer than its " ++ secs ++ " second " ++
          "budget\n  set EZ_DEADLINE higher if this tree honestly needs " ++
          "longer, or to 0 to stop asking\n")
        return V.tally(False{}, score)

# `ez test`: every test in the tree, all of them at once. Nothing here is
# ordered against anything else, since each test has its own scratch directory
# and port, and the report is still walked in the tree's order whatever order
# the jobs finished in.
def run() -> IO(Unit):  # noqa: L001 IO driver
  do IO<Unit>:
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +secs : String <- Timer.seconds()
    +deadline : String <- Timer.start(secs)
    +g : String <- Cap.gb()
    +at : String <- Env.lib()
    +jobs : String <- P.width()
    +ts : List<&2, String> <- find()
    P.fresh.dir(out.at())
    +by : String <- IO.pure(String, Clock.by.effect(deadline))
    as : List<&2, String> <- R.par(V.cmds(ts, cap, g, at), jobs, g, out.at(), by)
    every : V.Tally <- report(ts, as, V.Tally{0n, 0n})
    +late : Bool <- Timer.over(deadline)
    kept : V.Tally <- budget(late, secs, every)
    done(kept)

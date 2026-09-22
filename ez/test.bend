# ez/test: the test runner. Bend has none, so a test is a `*/tests/*.bend` file
# that prints, and states in a `#|` trailer the lines its run must print. Each
# test is its own `bend` run, since what these drive is git, nix and bend
# itself, and each wants its own process, scratch directory and port. A run
# disagreeing with its trailer is a failure, and any failure is a non-zero
# exit.
#
# Tests are not the proof gate. `ez prove` is, and nothing here runs a proof.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ./env.bend as Env
import ./cap.bend as Cap
import ./gate.bend as G
import ./quiet.bend as Q
import ./clock.bend as Clock
import ./prove.bend as P

# how many comparisons were made, and how many of them held
type Tally is Data:
  Tally{pass: Nat, total: Nat}

# a comparison that held says nothing. One that did not prints both sides in
# full: a diff is real work in Bend, and for a handful of short lines the pair
# reads better than one would.
def say(ok: Bool, name: String, want: String, got: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.write("FAIL: " ++ name ++ "\n  expected:\n" ++ P.indent(want) ++
        "  observed:\n" ++ P.indent(got))

# one more comparison, and one more pass when it held
def tally.go(ok: Bool, passed: Nat, total: Nat) -> Tally:
  match ok:
    case True{}:
      Tally{(1n + passed : Nat), (1n + total : Nat)}
    case False{}:
      Tally{passed, (1n + total : Nat)}

# the tally with this comparison's verdict in it
def tally(ok: Bool, score: Tally) -> Tally:
  Tally{p, n} = score
  tally.go(ok, p, n)

# what was wanted against what happened, reported and counted
def check(name: String, +wanted: String, +got: String, score: Tally) -> IO(Tally):
  do IO<Tally>:
    say(String.eq(wanted, got), name, wanted, got)
    return tally(String.eq(wanted, got), score)

# one test against its own trailer
def one(+path: String, +output: String, score: Tally) -> IO(Tally):
  do IO<Tally>:
    src : Maybe<&2, String> <- F.read(path)
    check(path, G.trailer(F.text_of(src)), Q.filter(R.text(output)), score)

# every test the answers ran out before. The two lists are the same length by
# construction and this should never have one to report, but the alternative to
# saying so is a green count over fewer tests than the tree holds, which is the
# worst answer a gate can give.
def short(ts: List<&2, String>, score: Tally) -> IO(Tally):
  match ts:
    case Nil{}:
      IO.pure(Tally, score)
    case Con{_h, rest}:
      do IO<Tally>:
        IO.write("FAIL: the run planned a test it never got an answer for\n")
        short(rest, tally(False{}, score))

# every test, in the tree's order however the run happened to interleave
def report(ts: List<&2, String>, as: List<&2, String>, score: Tally) -> IO(Tally):
  match ts as:
    case Con{+h, tt} Con{+x, xt}:
      do IO<Tally>:
        next : Tally <- one(h, x, score)
        report(tt, xt, next)
    case rest _x:
      short(rest, score)

# every test file
def find() -> IO(List<&2, String>):
  P.find.at("*/tests/*.bend", "-path")

# the count, and the exit status it implies. The reminder sits above the count
# and never below it: a run's last line is its verdict, and something reads it.
def done.go(+passed: Nat, +total: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.print("tests are a last resort for what you cannot prove")
    IO.print("PASS: " ++ Nat.show(passed) ++ " / " ++ Nat.show(total))
    P.done.exit(Nat.is_eq(passed, total))

# what a whole run amounts to
def done(score: Tally) -> IO(Unit):
  Tally{p, n} = score
  done.go(p, n)

# where the jobs of a run write what they print
def out.at() -> String:
  ".ez/run/test"

# the budget checked the way every other thing here is checked. A run that
# overran is a run that failed, and it says so in the count rather than merely
# taking a long time.
def budget(late: Bool, +secs: String, score: Tally) -> IO(Tally):
  match late:
    case False{}:
      IO.pure(Tally, score)
    case True{}:
      do IO<Tally>:
        IO.write("FAIL: the gate took longer than its " ++ secs ++ " second " ++
          "budget\n  set EZ_DEADLINE higher if this tree honestly needs " ++
          "longer, or to 0 to stop asking\n")
        return tally(False{}, score)

# `ez test`: every test in the tree, all of them at once. Nothing here is
# ordered against anything else, since each test has its own scratch directory
# and port, and the report is still walked in the tree's order whatever order
# the jobs finished in.
def run() -> IO(Unit):
  do IO<Unit>:
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +secs : String <- Clock.seconds()
    +deadline : String <- Clock.start(secs)
    +g : String <- Cap.gb()
    +at : String <- Env.lib()
    +jobs : String <- P.width()
    +ts : List<&2, String> <- find()
    P.fresh.dir(out.at())
    +by : String <- IO.pure(String, Clock.by.effect(deadline))
    as : List<&2, String> <- R.par(P.cmds(ts, cap, g, at), jobs, g, out.at(), by)
    every : Tally <- report(ts, as, Tally{0n, 0n})
    +late : Bool <- Clock.over(deadline)
    kept : Tally <- budget(late, secs, every)
    done(kept)

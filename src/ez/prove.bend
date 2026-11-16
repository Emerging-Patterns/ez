# ez/prove: the proof gate. Every PROOF.bend in the tree is run through `bend`,
# all of them at once, and a proof passes only when the first line bend prints
# is exactly `ALL PROOFS CHECK`. Nothing is cached: a gate CI leans on answers
# for the tree in front of it, not for one it saw before.
#
# The line is the verdict, never the exit status. Since bend 2.0.32 a file
# with no main is answered `ALL PROOFS CHECK` or `SOME PROOFS FAIL`, and a
# proof that reaches an `@unsafe` def or foreign code, imports included, fails
# and exits 1 rather than passing with a note as 2.0.31 did. The gate reads
# the line all the same: a status says nothing about what was checked, and
# only that first line says every term was proved outright.
#
# Trusted, not proved: `ez prove` runs `bend` on every PROOF.bend in the
# tree and passes only on an exact `ALL PROOFS CHECK` first line. It is ez
# code run by `mkProofs`, not a law. CI builds from a clean tree, so nothing
# is cached.
import Base
import snap@1.4.0.0/main.bend as R
import ../share/args.bend as Args
import ../share/env.bend as Env
import ../share/cap.bend as Cap
import ../share/capped.bend as Capped
import ./quiet.bend as Q
import ./sorted.bend as Sort
import ./verdict.bend as V
import ../ez/ends.bend as E
import ../lock/run.bend as Run

# every file of a kind in the tree, sorted, so a run's report is the same twice
# over. Base has no readdir, so this is `find`. `.claude` is skipped along with
# `.ez`: an agent's worktree is a whole second copy of the repo living inside
# it, and running its files would double the gate to check nothing new.
def find.at(+what: String, +how: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    out : String <- R.exec(["find", ".", how, what,
      "-not", "-path", "./.ez/*",
      "-not", "-path", "./.git/*", "-not", "-path", "./.claude/*"])
    return Sort.sort(Args.nonempty(String.lines(R.text(out))))

# every proof file
def find.proofs() -> IO(List<&2, String>):
  find.at("PROOF.bend", "-name")

# how many `bend` runs may be in flight at once. Empty is the usual answer and
# means the effect works it out: cores, but never more of them than the memory
# cap divides the machine into, since each one of these may claim the whole
# cap. EZ_JOBS overrides it for a machine that knows better.
def width() -> IO(String):  # noqa: L001 IO driver
  Env.var("EZ_JOBS", "")

# a directory emptied and made again, so nothing a run reads was written by the
# run before it
def fresh.dir(+at: String) -> IO(Unit):
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", at])
    _mk : String <- R.exec(["mkdir", "-p", at])
    return Unit{}

# where the jobs of this run write what they print
def out.at() -> String:
  ".ez/run/prove"

# one proof's line. A proof that held says so in one line; one that did not
# names itself and then prints what bend said, since that is where the law
# that failed is named.
def say(ok: Bool, +path: String, +text: String) -> IO(Unit):  # noqa: L001 IO driver
  match ok:
    case True{}:
      IO.print("ok: " ++ path)
    case False{}:
      IO.write("FAIL: " ++ path ++ "\n" ++ V.indent(text))

# one proof against its answer: the run's first line, with a memory kill turned
# into a sentence in front of what it printed
def one(+path: String, +gigs: String, +output: String, +passed: Nat) -> IO(Nat):  # noqa: L001 IO driver
  do IO<Nat>:
    +text : String <- IO.pure(String, R.text(output))
    +ok : Bool <- IO.pure(Bool, V.passed(text))
    say(ok, path, Capped.why(output, gigs) ++ Q.chomp(text))
    return V.count(ok, passed)

# every proof the answers ran out before. The two lists are the same length by
# construction and this should never have one to report, but the alternative
# to saying so is a green count over fewer proofs than the tree holds.
def short(ps: List<&2, String>) -> IO(Unit):  # noqa: L001 IO driver
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, t}:
      do IO<Unit>:
        IO.print("FAIL: " ++ h ++ ": the run never answered for it")
        short(t)

# every proof, in the tree's order however the run happened to interleave
def report(ps: List<&2, String>, as: List<&2, String>, +gigs: String, +passed: Nat) -> IO(Nat):  # noqa: L001 IO driver
  match ps as:
    case Con{+h, pt} Con{+x, xt}:
      do IO<Nat>:
        next : Nat <- one(h, gigs, x, passed)
        report(pt, xt, gigs, next)
    case rest _x:
      do IO<Nat>:
        short(rest)
        return passed

# the count, and the exit status it implies. A run's last line is its verdict,
# and anything that failed fails the command (`E.counted`), or a script around
# it learns nothing.
def done(+passed: Nat, +total: Nat) -> IO(Unit):  # noqa: L001 IO driver
  do IO<Unit>:
    IO.print("PASS: " ++ Nat.show(passed) ++ " / " ++ Nat.show(total))
    Run.end(E.counted(passed, total))

# `ez prove`: every PROOF.bend in the tree, run at once and reported in the
# tree's order. There is no budget: a proof that takes long is still a proof,
# and one that never finishes is stopped by whatever runs the gate.
def run() -> IO(Unit):  # noqa: L001 IO driver
  do IO<Unit>:
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +g : String <- Cap.gb()
    +at : String <- Env.lib()
    +jobs : String <- width()
    +ps : List<&2, String> <- find.proofs()
    fresh.dir(out.at())
    as : List<&2, String> <- R.par(V.cmds(ps, cap, g, at), jobs, g, out.at(), "0")
    +passed : Nat <- report(ps, as, g, 0n)
    done(passed, List.length(&2, String, ps))

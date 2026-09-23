# ez/prove: the proof gate. Every PROOF.bend in the tree is run through `bend`,
# all of them at once, and a proof passes only when the first line bend prints
# is exactly `All terms check.` Nothing is cached: a gate CI leans on answers
# for the tree in front of it, not for one it saw before.
#
# The line is the verdict, never the exit status. Both
# `All terms check, with N unsafe annotations.` and 2.0.18's
# `All terms check, but N defs rely on unsafe or foreign code:` exit 0, so a
# gate reading the status alone goes green on a claim that leans on code
# nothing proved. Only the bare line means every term was proved outright.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../ez/args.bend as Args
import ../ez/env.bend as Env
import ../ez/cap.bend as Cap
import ./quiet.bend as Q
import ./sorted.bend as Sort
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
def width() -> IO(String):
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

# the first line of a run's output
def head.of(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> _t:
      h

# the first line of some text
def head(text: String) -> String:
  head.of(String.lines(text))

# the one line a proof passes on
def verdict() -> String:
  "All terms check."

# every line of a block, indented under the line that introduces it
def indent.go(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case h <> t:
      ("    " ++ h ++ "\n") <> indent.go(t)

# a block of text, indented
def indent(text: String) -> String:
  String.concat(indent.go(String.lines(text)))

# a `bend` on one file, inside the memory cap and with this project's BEND_LIB
# set for it
def cmd(cap: Bool, +gigs: String, +at: String, +path: String) -> List<&2, String>:
  Cap.argv(cap, gigs, at, ["bend", path])

# every file's command, in the tree's order
def cmds(ps: List<&2, String>, +cap: Bool, +gigs: String, +at: String) -> List<&2, List<&2, String>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      cmd(cap, gigs, at, h) <> cmds(t, cap, gigs, at)

# one proof's line. A proof that held says so in one line; one that did not
# names itself and then prints what bend said, since that is where the law
# that failed is named.
def say(ok: Bool, +path: String, +text: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("ok: " ++ path)
    case False{}:
      IO.write("FAIL: " ++ path ++ "\n" ++ indent(text))

# one more proof counted, and one more pass when it held
def count(ok: Bool, +passed: Nat) -> Nat:
  Bool.pick(Nat, ok, (1n + passed : Nat), passed)

# one proof against its answer: the run's first line, with a memory kill turned
# into a sentence in front of what it printed
def one(+path: String, +gigs: String, +output: String, +passed: Nat) -> IO(Nat):
  do IO<Nat>:
    +text : String <- IO.pure(String, R.text(output))
    +ok : Bool <- IO.pure(Bool, String.eq(head(text), verdict()))
    say(ok, path, Cap.why(output, gigs) ++ Q.chomp(text))
    return count(ok, passed)

# every proof the answers ran out before. The two lists are the same length by
# construction and this should never have one to report, but the alternative
# to saying so is a green count over fewer proofs than the tree holds.
def short(ps: List<&2, String>) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, t}:
      do IO<Unit>:
        IO.print("FAIL: " ++ h ++ ": the run never answered for it")
        short(t)

# every proof, in the tree's order however the run happened to interleave
def report(ps: List<&2, String>, as: List<&2, String>, +gigs: String, +passed: Nat) -> IO(Nat):
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
def done(+passed: Nat, +total: Nat) -> IO(Unit):
  do IO<Unit>:
    IO.print("PASS: " ++ Nat.show(passed) ++ " / " ++ Nat.show(total))
    Run.end(E.counted(passed, total))

# `ez prove`: every PROOF.bend in the tree, run at once and reported in the
# tree's order. There is no budget: a proof that takes long is still a proof,
# and one that never finishes is stopped by whatever runs the gate.
def run() -> IO(Unit):
  do IO<Unit>:
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +g : String <- Cap.gb()
    +at : String <- Env.lib()
    +jobs : String <- width()
    +ps : List<&2, String> <- find.proofs()
    fresh.dir(out.at())
    as : List<&2, String> <- R.par(cmds(ps, cap, g, at), jobs, g, out.at(), "0")
    +passed : Nat <- report(ps, as, g, 0n)
    done(passed, List.length(&2, String, ps))

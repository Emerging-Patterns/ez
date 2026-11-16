# ez/verdict: what the two runners read off a run. `ez prove` passes a proof
# whose first line is exactly `ALL PROOFS CHECK` and counts it; `ez test`
# tallies each comparison of a run with its trailer. Both runners print what
# failed indented under the line that names it. All of it is pure, so what a
# run is judged and counted as is a law (laws/ProofPassesOnVerdictLine.bend,
# laws/TestTallyCounts.bend); running `bend` and reading its output is the
# runners' (ez/prove.bend, ez/test.bend).
import Base
import ../share/capped.bend as Capped

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
  "ALL PROOFS CHECK"

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

# whether a run passed the proof gate: its first line is the verdict, exactly
def passed(text: String) -> Bool:
  String.eq(head(text), verdict())

# one more proof counted, and one more pass when it held
def count(ok: Bool, +passed: Nat) -> Nat:
  Bool.pick(Nat, ok, (1n + passed : Nat), passed)

# how many comparisons were made, and how many of them held
type Tally is Data:
  Tally{pass: Nat, total: Nat}

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

# a `bend` on one file, inside the memory cap and with this project's BEND_LIB
# set for it
def cmd(cap: Bool, +gigs: String, +at: String, +path: String) -> List<&2, String>:
  Capped.argv(cap, gigs, at, ["bend", path])

# every file's command, in the tree's order
def cmds(ps: List<&2, String>, +cap: Bool, +gigs: String, +at: String) -> List<&2, List<&2, String>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      cmd(cap, gigs, at, h) <> cmds(t, cap, gigs, at)

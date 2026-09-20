# ez/quiet: bend's check report dropped from a run's output, so a test sees only
# what its program printed. The wording changed between releases: 2.0.16 says
# `All terms check, with N unsafe annotations.` on one line, 2.0.18 says
# `All terms check, but N defs rely on unsafe or foreign code:` and then a
# `- <name>` line each. Both go. A test asserting its own output never starts a
# line with `- `.
import Base

# a trailing run of blank lines, being dropped from the right. `live` turns true
# at the first line that survives, after which nothing is dropped.
type Tail is Data:
  Tail{live: Bool, out: List<&2, String>}

# whether this line is part of the check report rather than the program's
# output. `report` says the line before it was.
def in_report(report: Bool, +line: String) -> Bool:
  Bool.or(String.starts_with(line, "All terms check"),
    Bool.and(report, String.starts_with(line, "- ")))

# a line kept or dropped
def put(drop: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match drop:
    case True{}:
      rest
    case False{}:
      h <> rest

# the lines with the report dropped. The state is decided once per line and
# used both for this line and for the next, so the walk needs no second pass.
# The list comes first because a self-call must shrink an argument before it
# changes one.
def go(ls: List<&2, String>, report: Bool) -> List<&2, String>:
  match ls:
    case []:
      []
    case +h <> t:
      +drop = in_report(report, h)
      put(drop, h, go(t, drop))

# a blank line: kept once something after it has survived, dropped while the
# run of trailing blanks is still open
def tail.blank(live: Bool, out: List<&2, String>) -> Tail:
  match live:
    case True{}:
      Tail{True{}, "" <> out}
    case False{}:
      Tail{False{}, out}

# one line offered to the tail. The line is taken apart rather than asked about,
# because a fold's step may not declare a `+` parameter to duplicate it.
def tail.line(h: String, live: Bool, out: List<&2, String>) -> Tail:
  match h:
    case SNil{}:
      tail.blank(live, out)
    case SCon{c, t}:
      Tail{True{}, SCon{c, t} <> out}

# a fold from the right: until a line survives, a blank one is dropped
def tail.step(h: String, st: Tail) -> Tail:
  Tail{live, out} = st
  tail.line(h, live, out)

# what a finished fold collected
def tail.out(st: Tail) -> List<&2, String>:
  Tail{_live, out} = st
  out

# the lines with the blank ones at the end dropped, the way a shell's `$(...)`
# drops a trailing newline, so a comparison never turns on one
def chomp.lines(ls: List<&2, String>) -> List<&2, String>:
  tail.out(List.foldr(~&2, ~String, ~Tail, ~tail.step, ls, Tail{False{}, []}))

# the text with its trailing blank lines dropped
def chomp(text: String) -> String:
  String.join(chomp.lines(String.lines(text)), "\n")

# a run's output as a test's `#|` trailer states it: no check report, no
# trailing newline
def filter(text: String) -> String:
  String.join(chomp.lines(go(String.lines(text), False{})), "\n")

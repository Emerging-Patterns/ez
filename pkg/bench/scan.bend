# pkg/bench/scan: what classifying the lines of a source file costs.
#
# This is not a test and the gate does not collect it. It lives in `bench/`
# rather than `tests/` for net/bench/dechunk.bend's reason: `ez test` runs
# every `*/tests/*.bend` on both lanes, and an input big enough to show the
# cost would add minutes to the gate to assert nothing pkg/tests/scan.bend
# does not already assert.
#
#   bend pkg/bench/scan.bend -o /tmp/scan
#   /tmp/scan new 200000    # the classifier as pkg/pkg.bend has it now
#   /tmp/scan old 200000    # the classifier as it was, for the difference
#
# The input is `n` copies of a ten-line block written the way this repo is
# written: two lines of comment, a blank, a seven-line def. Four of the ten
# are lines `quiet` exists to skip, which is the ratio that matters, because
# the whole of the rewrite is that a line it skips no longer gets split into
# words and classified on the way to being skipped.
#
# ez walks this classifier over every `.bend` file of the project and of every
# package it resolves, on every `ez lock` and every `ez fetch`, so the input
# is the number of source lines in a project rather than anything exotic.
#
# What it said, built native, on 200000 blocks, which is two million lines:
#
#   old 200000    5.06 s
#   new 200000    3.29 s
#
# Both print 1200000, the six lines a block that say something, so the
# classification happened and the rewrite did not change an answer. A 1.54x
# saving over the whole scan. Nothing here is quadratic; what changed is that
# most of the work was being done for lines about to be thrown away.
import Base
import ../pkg.bend as P

# an `import <spec> as <Name>` line, before: the word is read out of the list
# whether or not the line turned out to name a module
def old.mod_of(+ws: List<&2, String>) -> P.Stmt:
  Bool.pick(P.Stmt,
    Bool.and(Nat.is_ge(List.length(&2, String, ws), 4n),
      Bool.and(String.eq(P.word(ws, 0n), "import"),
        String.eq(P.word(ws, 2n), "as"))),
    P.SMod{P.word(ws, 1n)}, P.SBody{})

# the prelude, before: `mod_of` runs for `import Base` too
def old.base_of(+ws: List<&2, String>) -> P.Stmt:
  Bool.pick(P.Stmt,
    Bool.and(Nat.is_eq(List.length(&2, String, ws), 2n),
      Bool.and(String.eq(P.word(ws, 0n), "import"),
        String.eq(P.word(ws, 1n), "Base"))),
    P.SNone{}, old.mod_of(ws))

# the classifier, before: `words(s)` is a `String.split` and a filter over its
# result, and it sits in an arm of a `Bool.pick`, so it runs for every blank
# line and every comment line as well
def old.stmt_of(+s: String) -> P.Stmt:
  Bool.pick(P.Stmt,
    Bool.and(String.starts_with(s, "import \""), String.ends_with(s, "\"")),
    P.SForeign{String.take(String.drop(s, 8n), Nat.sub(String.length(s), 9n))},
    Bool.pick(P.Stmt, P.quiet(s), P.SNone{}, old.base_of(P.words(s))))

# one block of source as this repo writes it: two lines of comment, a blank, a
# def of seven lines, and the blank that follows it
def block() -> List<&2, String>:
  ["# what this def is for, said at about the length the repo says it at",
   "# and a second line of the same, because most comments here run to two",
   "",
   "def some.name(+x: String, y: Nat) -> String:",
   "  match y:",
   "    case 0n:",
   "      x",
   "    case 1n+p:",
   "      some.name(x, p)",
   ""]

# `n` blocks of it
def lines.go(n: Nat, +one: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      []
    case 1n+p:
      List.append(&2, String, one, lines.go(p, one))

# the source, built once so both modes classify the same lines
def lines(n: Nat) -> List<&2, String>:
  lines.go(n, block())

# a line that said something about the header counts one, a line that said
# nothing counts none. The count is what makes the classification observable:
# a reviewer can see it happened and was not skipped, and both modes must
# print the same number or the rewrite changed an answer.
def tally(st: P.Stmt) -> Nat:
  match st:
    case P.SNone{}:
      0n
    case P.SMod{_spec}:
      1n
    case P.SForeign{_at}:
      1n
    case P.SBody{}:
      1n

# every line classified, the new way
def count.new(ls: List<&2, String>) -> Nat:
  match ls:
    case []:
      0n
    case h <> t:
      Nat.add(tally(P.stmt_of(String.trim(h))), count.new(t))

# every line classified, the old way
def count.old(ls: List<&2, String>) -> Nat:
  match ls:
    case []:
      0n
    case h <> t:
      Nat.add(tally(old.stmt_of(String.trim(h))), count.old(t))

# the answer a mode asks for. Both modes build the same lines, so the
# difference between the two timings is the classifier alone.
def run.at(old: Bool, n: Nat) -> String:
  match old:
    case True{}:
      "old " ++ Nat.show(count.old(lines(n)))
    case False{}:
      "new " ++ Nat.show(count.new(lines(n)))

# the mode named on the command line, answered
def run(mode: String, n: Nat) -> String:
  run.at(String.eq(mode, "old"), n)

# a &1 list copied into a &2 one, since `IO.args()` answers a list read once
def copy(xs: List<&1, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> copy(t)

# the nth argument, "" past the end
def at(xs: List<&2, String>, n: Nat) -> String:
  match xs n:
    case Nil{} 0n:
      ""
    case Nil{} 1n+p:
      ""
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      at(t, p)

# the command line: a mode, and how many blocks of source to classify
def start(as: List<&2, String>) -> IO(Unit):
  match as:
    case Nil{}:
      IO.print(run("new", U32.to_nat(200000)))
    case Con{h, t}:
      IO.print(run(h,
        U32.to_nat(Maybe.default(&2, U32, U32.read(at(t, 0n)), 200000))))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&1, String> <- IO.args()
    start(copy(xs))

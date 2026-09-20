# manifest/bench/parse: what classifying the lines of a lockfile costs.
#
# This is not a test and the gate does not collect it, for the reason
# net/bench/dechunk.bend gives: `ez test` runs every `*/tests/*.bend` on both
# lanes, and a lock big enough to show the cost would add minutes to the gate
# to assert nothing manifest/tests/parse.bend already asserts.
#
#   bend manifest/bench/parse.bend -o /tmp/parse
#   /tmp/parse new 100000    # the classifier as manifest/toml.bend has it now
#   /tmp/parse old 100000    # the classifier as it was, for the difference
#
# The input is `n` copies of the stanza `ez lock` writes for one package: a
# comment, a header, four pairs and a blank. Two of the seven lines are ones
# `line_of` answers without reading anything out of them, and under the old
# nested `Bool.pick` those two still paid for a `head_of` and a
# `String.split` each, because `Bool.pick` is an ordinary function and builds
# every arm of the nest before any condition is consulted.
#
# What it said, built native, on 100000 stanzas, which is 700000 lines:
#
#   old 100000    4.53 s
#   new 100000    2.32 s
#
# Both print 500000, the five lines a stanza that are a header or a pair, so
# the classification happened and the rewrite did not change an answer. A
# 1.95x saving on the classifier. A real `ez.lock.toml` of fifty packages is
# a few hundred lines, so this is not a wall anyone has hit; it is a constant
# factor on a parse ez runs on every `ez fetch` and every `ez lock`, and the
# rewrite is also the shorter code.
import Base
import ../toml.bend as T

# the classifier, before: four `Bool.pick`s nested, so `head_of(s, ...)` and
# `pair_of(String.split(s, '='))` were both built for every line, including
# the blanks and the comments the first two arms exist to answer
def old.line_of(+s: String) -> T.Line:
  Bool.pick(T.Line, String.is_empty(s), T.LSkip{},
    Bool.pick(T.Line, String.starts_with(s, "#"), T.LSkip{},
      Bool.pick(T.Line, String.starts_with(s, "["),
        T.head_of(s, String.ends_with(s, "]")),
        Bool.pick(T.Line, String.contains(s, "="),
          T.pair_of(String.split(s, '=')),
          T.LBad{s ++ " is neither a section header nor a key"}))))

# the stanza `ez lock` writes for one package
def stanza() -> List<&2, String>:
  ["# the package and where it came from",
   "[[package]]",
   "hash = \"0x0a5c1d9f3b7e2c48a6d0f1e5b9c3a7d2\"",
   "source = \"git\"",
   "url = \"https://example.invalid/some/repository\"",
   "rev = \"3f1c9a2b8d4e6075c1a9b3d8e2f4607a5c1b9d3e\"",
   ""]

# `n` of them
def lines.go(n: Nat, +one: List<&2, String>) -> List<&2, String>:
  match n:
    case 0n:
      []
    case 1n+p:
      List.append(&2, String, one, lines.go(p, one))

# the lock, built once so both modes classify the same lines
def lines(n: Nat) -> List<&2, String>:
  lines.go(n, stanza())

# a header or a pair counts one, a skipped or a bad line counts none. The
# count is what makes the classification observable, and both modes must
# print the same number or the rewrite changed an answer.
def tally(l: T.Line) -> Nat:
  match l:
    case T.LSkip{}:
      0n
    case T.LHead{_name}:
      1n
    case T.LPair{_key, _val}:
      1n
    case T.LBad{_why}:
      0n

# every line classified, the new way
def count.new(ls: List<&2, String>) -> Nat:
  match ls:
    case []:
      0n
    case h <> t:
      Nat.add(tally(T.line_of(T.trim(h))), count.new(t))

# every line classified, the old way
def count.old(ls: List<&2, String>) -> Nat:
  match ls:
    case []:
      0n
    case h <> t:
      Nat.add(tally(old.line_of(T.trim(h))), count.old(t))

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

# the command line: a mode, and how many stanzas the lock holds
def start(as: List<&2, String>) -> IO(Unit):
  match as:
    case Nil{}:
      IO.print(run("new", U32.to_nat(100000)))
    case Con{h, t}:
      IO.print(run(h,
        U32.to_nat(Maybe.default(&2, U32, U32.read(at(t, 0n)), 100000))))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<&1, String> <- IO.args()
    start(copy(xs))

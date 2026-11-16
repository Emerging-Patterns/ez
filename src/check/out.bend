# check/out: what an end-to-end test reads out of a program's answer, and the
# command lines it builds. A snap answer is a status line and then what the
# program printed; these pick lines out of the printed part and values out of
# `key = "value"` lines. They are pure, so a law reaches them without the
# programs check/world.bend runs.
import Base
import snap@1.4.0.0/src/answer.bend as A

# the non-empty strings, which is what a program's output amounts to once its
# trailing newline has been counted as a line
def nonblank(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = nonblank(t)
      Bool.pick(List<&2, String>, String.is_empty(h), more, h <> more)

# the first line of a list of them
def first(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> t:
      h

# a one-line answer, without the newline the program ended it with
def line(+out: String) -> String:
  first(String.lines(A.text(out)))

# the last line of a list of them
def last(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case Con{h, Nil{}}:
      h
    case Con{_h, t}:
      last(t)

# the last thing a program said, which for one that reports as it goes is its
# answer
def tail(+out: String) -> String:
  last(String.lines(A.text(out)))

# the nth of a list of strings, or "" when there is no such one. The list and
# the count are scrutinised together, so the walk needs no helper to branch.
def nth(ls: List<&2, String>, index: Nat) -> String:
  match ls index:
    case Nil{} _m:
      ""
    case Con{h, _t} 0n:
      h
    case Con{_h, t} 1n+p:
      nth(t, p)

# one step of a search for the first line that answers. Both searches here
# want it, so it is stated once.
#
# A recursive call in an arm of a `Bool.pick` is not an arm: `Bool.pick` is an
# ordinary function, so both arms are built before it picks one and the line
# found first still costs a walk of every line after it. The rest of the
# search arrives as a thunk, which is a value, and only the arm that wants it
# applies it.
def first.step(here: Bool, text: String, rest: Unit -> String) -> String:
  match here:
    case True{}:
      text
    case False{}:
      rest(Unit{})

# the first line that starts with this, or "" when none does
def starting(ls: List<&2, String>, +pre: String) -> String:
  match ls:
    case []:
      ""
    case +h <> t:
      first.step(String.starts_with(h, pre), h, _u => starting(t, pre))

# the first line that holds this anywhere in it, or "" when none does
def containing(ls: List<&2, String>, +sub: String) -> String:
  match ls:
    case []:
      ""
    case +h <> t:
      first.step(String.contains(h, sub), h, _u => containing(t, sub))

# the last line that starts with this, or "" when none does. A build's answer
# is the last thing it says, because its log arrives on the same stream.
def starting.last(ls: List<&2, String>, +pre: String, got: String) -> String:
  match ls:
    case []:
      got
    case +h <> t:
      starting.last(t, pre, Bool.pick(String, String.starts_with(h, pre), h, got))

# what a `key = "value"` line holds, which is all ez's own files ever hold
def quoted(+row: String) -> String:
  nth(String.split(row, '"'), 1n)

# the value a text gives a key, over its `key = "value"` lines
def value(+text: String, +key: String) -> String:
  quoted(starting(String.lines(text), key))

# a command run in a directory, with the gate's BEND_LIB taken away. Base has
# no chdir, so the directory is `env`'s business; and a test that is about
# where packages come from must not inherit the one the gate set for itself.
def inside(at: String, args: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, ["env", "-C", at, "-u", "BEND_LIB"], args)

# `ez` run in a project directory. The binary is the whole of ez, so it is
# started with nothing in front of it but the directory it runs in.
def ez(+repo: String, +app: String, args: List<&2, String>) -> List<&2, String>:
  inside(app, List.append(&2, String, [repo ++ "/bin/ez.bin"], args))

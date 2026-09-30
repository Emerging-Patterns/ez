# ez/gate: what a test file says its run must print. A test states that in a
# `#|` trailer, one line for each line of output, and `ez test` holds the run
# to it.
#
# This file imports nothing but Base, so a law about the trailer walk costs a
# compile of that and no more.
import Base

# a trailer line kept, with its `#|` dropped, or a source line ignored
def want.put(is_want: Bool, line: String, rest: List<&2, String>) -> List<&2, String>:
  match is_want:
    case True{}:
      String.drop(line, 2n) <> rest
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

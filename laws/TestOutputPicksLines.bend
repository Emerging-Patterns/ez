# How an end-to-end test reads a program's answer and builds the command lines
# it runs (src/check/out.bend). This is internal: the tests are host checks,
# never evidence for a guarantee, and these laws only hold their reading in
# place so a test that fails is about ez.
#
# A snap answer is a status line and then what the program printed. A test's
# one-line answer is the first line printed, and a program that reports as it
# goes answers with its last. Empty lines are dropped where a test counts what
# a program listed, and every other line kept in order. A search for a line
# that starts with, or holds, a text gives the first line that does, or "". A
# `key = "value"` line's value is what stands between its first two quotes.
# Every command a test runs inside a project runs there through `env -C` with
# BEND_LIB taken away, and `ez` is the repo's own built binary.
import Base
import snap@1.6.0.0/src/answer.bend as A
import ../src/check/out.bend as O

# LAW: an empty line is dropped
law nonblank_drops:
  for +line: String
  for rest: List<&2, String>
  for empty: {True{} == String.is_empty(line) : Bool}
  {O.nonblank(line <> rest) == O.nonblank(rest) : List<&2, String>}

# LAW: any other line is kept, in front of what the rest keeps
law nonblank_keeps:
  for +line: String
  for rest: List<&2, String>
  for full: {False{} == String.is_empty(line) : Bool}
  {O.nonblank(line <> rest) == line <> O.nonblank(rest) : List<&2, String>}

# LAW: the first of the lines is the first
law first_line:
  for line: String
  for rest: List<&2, String>
  {O.first(line <> rest) == line : String}

# LAW: a one-line answer is the first line the program printed
law line_is_first:
  for +out: String
  {O.line(out) == O.first(String.lines(A.text(out))) : String}

# LAW: the last of one line is that line
law last_one:
  for line: String
  {O.last([line]) == line : String}

# LAW: the last of more lines is the last of the ones after the first
law last_more:
  for line: String
  for next: String
  for rest: List<&2, String>
  {O.last(line <> (next <> rest)) == O.last(next <> rest) : String}

# LAW: a reported answer is the last line the program printed
law tail_is_last:
  for +out: String
  {O.tail(out) == O.last(String.lines(A.text(out))) : String}

# LAW: the line at index zero is the first
law nth_first:
  for line: String
  for rest: List<&2, String>
  {O.nth(line <> rest, 0n) == line : String}

# LAW: the line at the next index is the one at that index of the rest
law nth_next:
  for line: String
  for rest: List<&2, String>
  for index: Nat
  {O.nth(line <> rest, 1n+index) == O.nth(rest, index) : String}

# LAW: a line that starts with the text is the one found
law starting_hit:
  for +line: String
  for rest: List<&2, String>
  for +pre: String
  for hit: {True{} == String.starts_with(line, pre) : Bool}
  {O.starting(line <> rest, pre) == line : String}

# LAW: one that does not is passed over
law starting_miss:
  for +line: String
  for rest: List<&2, String>
  for +pre: String
  for miss: {False{} == String.starts_with(line, pre) : Bool}
  {O.starting(line <> rest, pre) == O.starting(rest, pre) : String}

# LAW: a line that holds the text is the one found
law containing_hit:
  for +line: String
  for rest: List<&2, String>
  for +sub: String
  for hit: {True{} == String.contains(line, sub) : Bool}
  {O.containing(line <> rest, sub) == line : String}

# LAW: one that does not is passed over
law containing_miss:
  for +line: String
  for rest: List<&2, String>
  for +sub: String
  for miss: {False{} == String.contains(line, sub) : Bool}
  {O.containing(line <> rest, sub) == O.containing(rest, sub) : String}

# LAW: a key's value is read off the first line that starts with the key, as
# what stands between its first two quotes
law value_reads:
  for +text: String
  for +key: String
  {O.value(text, key) == O.nth(String.split(O.starting(String.lines(text), key), '"'), 1n)
    : String}

# LAW: a command runs in its directory with BEND_LIB taken away, its words
# after that as they were given
law inside_env:
  for at: String
  for args: List<&2, String>
  {O.inside(at, args) == "env" <> ("-C" <> (at <> ("-u" <> ("BEND_LIB" <> args))))
    : List<&2, String>}

# LAW: `ez` in a project is the repo's own binary, run inside it
law ez_runs_bin:
  for +repo: String
  for +app: String
  for args: List<&2, String>
  {O.ez(repo, app, args) == O.inside(app, (repo ++ "/bin/ez.bin") <> args) : List<&2, String>}

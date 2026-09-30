# pub/blurb: the line the hub shows as a package's description, pure. The
# hub takes the first line of the package's first file by path, in plain
# string order (so an uppercase letter comes before every lowercase one), and
# passes over a file named LICENSE, which bend 2.0.27 sends beside the files
# it publishes. `ez publish` says this line before it uploads (pub/plan.bend),
# and `ez init` opens the entry it writes with a line of its own for it
# (init/plan.bend), so the line a project is shown by on the hub is one its
# author wrote.
#
# Paths are compared with `String.is_le`, the order the package walk writes a
# manifest in (`K.file.le`). It compares characters by code point, which is
# JavaScript's order for every path whose characters are all in the Basic
# Multilingual Plane.
import Base
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path

# one step of a scan for a newline, with the head's answer in hand; the rest
# arrives as a thunk, so the first newline ends the scan
def nl.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a text holds a newline, so is more than one line
def has.nl(text: String) -> Bool:
  match text:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      nl.step(Char.is_eq(h, '\n'), _u => has.nl(t))

# one step of the first line: a newline ends it, and any other character
# starts what the rest of the line is
def line.step(end: Bool, +head: Char, rest: Unit -> String) -> String:
  match end:
    case True{}:
      SNil{}
    case False{}:
      SCon{head, rest(Unit{})}

# a text's first line: everything before its first newline, the whole text
# when it has none
def line.first(text: String) -> String:
  match text:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      line.step(Char.is_eq(h, '\n'), h, _u => line.first(t))

# whether a file of a package is a LICENSE, which the hub passes over
def lic(file: K.Source) -> Bool:
  K.Source{at, _text} = file
  String.eq(Path.base(at), "LICENSE")

# where a file stands in the hub's order
def at(file: K.Source) -> String:
  K.Source{a, _text} = file
  a

# the earlier of the file found so far and the next one; a tie keeps the one
# found first
def least.vs(cur: Maybe<&2, K.Source>, +next: K.Source) -> Maybe<&2, K.Source>:
  match cur:
    case None{}:
      Some{next}
    case Some{+c}:
      Bool.pick(Maybe<&2, K.Source>, String.is_le(at(c), at(next)), Some{c}, Some{next})

# the next file weighed: a LICENSE is passed over, and any other file is the
# earlier of itself and the one found so far
def least.pick(skip: Bool, cur: Maybe<&2, K.Source>, +next: K.Source) -> Maybe<&2, K.Source>:
  match skip:
    case True{}:
      cur
    case False{}:
      least.vs(cur, next)

# the first file by path among these and the one found so far, LICENSE files
# passed over
def least(fs: List<&2, K.Source>, cur: Maybe<&2, K.Source>) -> Maybe<&2, K.Source>:
  match fs:
    case []:
      cur
    case +h <> t:
      least(t, least.pick(lic(h), cur, h))

# a file's first line
def line.file(file: K.Source) -> String:
  K.Source{_at, text} = file
  line.first(text)

# the first line of the file found, "" when there is none
def line.of(got: Maybe<&2, K.Source>) -> String:
  match got:
    case None{}:
      ""
    case Some{f}:
      line.file(f)

# the line the hub describes a package by: the first line of its first file
# by path that is not a LICENSE
def blurb(fs: List<&2, K.Source>) -> String:
  line.of(least(fs, None{}))

# one step of the walk below, with the head's answer in hand; the rest
# arrives as a thunk, so the first file that comes earlier ends the walk
def after.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# whether every file of these comes no earlier than a path, a LICENSE
# included. Law vocabulary: a file whose path is this one comes first.
def after(+path: String, fs: List<&2, K.Source>) -> Bool:
  match fs:
    case []:
      True{}
    case +h <> t:
      after.step(String.is_le(path, at(h)), _u => after(path, t))

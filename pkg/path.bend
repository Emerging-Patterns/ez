# pkg/path: the path arithmetic the import walk needs, lexical only. Base has
# no readdir and no realpath, and a module's name in a package is the path it
# was reached through, so `.` and `..` are resolved by text rather than by
# asking the file system.
import Base

# where a normalisation has got to: `abs` is true for a path that began at the
# root, `out` the components kept so far, reversed
type Walk is Data:
  Walk{abs: Bool, out: List<&2, String>}

# what one component of a path turned out to be
type Comp is Data:
  CSkip{}
  CUp{}
  CName{s: String}

# a component classified. `+c` because it is both asked about and kept.
def comp_of(+c: String) -> Comp:
  Bool.pick(Comp, Bool.or(String.is_empty(c), String.eq(c, ".")), CSkip{},
    Bool.pick(Comp, String.eq(c, ".."), CUp{}, CName{c}))

# a climb with nothing left to climb off: at the root it goes nowhere, and in a
# relative path it is kept, since the package may still be re-rooted under it
def up.root(abs: Bool) -> List<&2, String>:
  match abs:
    case True{}:
      []
    case False{}:
      [".."]

# a climb past a component that is itself a climb keeps both
def up.back(same: Bool, h: String, t: List<&2, String>) -> List<&2, String>:
  match same:
    case True{}:
      ".." <> (h <> t)
    case False{}:
      t

# a climb against what has been kept: it cancels the last real component
def up.go(+h: String, t: List<&2, String>) -> List<&2, String>:
  up.back(String.eq(h, ".."), h, t)

# a climb against what has been kept
def up(abs: Bool, out: List<&2, String>) -> List<&2, String>:
  match out:
    case []:
      up.root(abs)
    case h <> t:
      up.go(h, t)

# a climb, with the root flag carried through
def up.step(+abs: Bool, out: List<&2, String>) -> Walk:
  Walk{abs, up(abs, out)}

# the state once a component has been classified
def norm.go(st: Walk, c: Comp) -> Walk:
  Walk{abs, out} = st
  match c:
    case CSkip{}:
      Walk{abs, out}
    case CUp{}:
      up.step(abs, out)
    case CName{s}:
      Walk{abs, s <> out}

# one component against the state
def norm.step(st: Walk, c: String) -> Walk:
  norm.go(st, comp_of(c))

# a relative path with nothing left in it is the current directory
def norm.rel(+body: String) -> String:
  Bool.pick(String, String.is_empty(body), ".", body)

# the components put back together, under the root or not
def norm.text(abs: Bool, body: String) -> String:
  match abs:
    case True{}:
      "/" ++ body
    case False{}:
      norm.rel(body)

# the components a normalisation kept, in order
def norm.fin(st: Walk) -> String:
  Walk{abs, out} = st
  norm.text(abs, String.join(List.reverse(&2, String, out), "/"))

# a path with `.` and an inner `..` resolved by text. A leading `..` survives,
# because a module reached through one re-roots the package rather than
# escaping it.
def norm(+p: String) -> String:
  norm.fin(List.foldl(~&2, ~String, ~Walk, ~norm.step, String.split(p, '/'),
    Walk{String.starts_with(p, "/"), []}))

# the last component of a path
def base.last(ps: List<&2, String>) -> String:
  match ps:
    case []:
      ""
    case Con{h, Nil{}}:
      h
    case Con{_h, t}:
      base.last(t)

# the last component of a path
def base(p: String) -> String:
  base.last(String.split(p, '/'))

# the path with its last component climbed back off
def dir(+p: String) -> String:
  norm(p ++ "/..")

# a path taken relative to a directory. An empty directory means the path is
# already where it should be, and never that it starts at the root.
def join(+a: String, +b: String) -> String:
  Bool.pick(String, String.is_empty(a), norm(b), norm(a ++ "/" ++ b))

# the last `n` components of a path
def tail(p: String, n: Nat) -> String:
  String.join(List.reverse(&2, String,
    List.take(&2, String, List.reverse(&2, String, String.split(p, '/')), n)), "/")

# whether a component is a climb
def up.is(s: String) -> Bool:
  String.eq(s, "..")

# how many components of a path are climbs
def ups(p: String) -> Nat:
  List.length(&2, String, List.filter(~String, ~up.is, String.split(p, '/')))

# a module path without its `.bend`, which is how bend names the module
def unbend(+p: String) -> String:
  Bool.pick(String, String.ends_with(p, ".bend"),
    String.take(p, Nat.sub(String.length(p), 5n)), p)

# the path with `n` of its components climbed back off, which is where a
# package re-roots when a module of it was reached through that many `..`
def climb(n: Nat, p: String) -> String:
  match n:
    case 0n:
      norm(p)
    case 1n+q:
      climb(q, dir(p))

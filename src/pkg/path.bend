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
def comp_of(+part: String) -> Comp:
  Bool.pick(Comp, Bool.or(String.is_empty(part), String.eq(part, ".")), CSkip{},
    Bool.pick(Comp, String.eq(part, ".."), CUp{}, CName{part}))

# a climb with nothing left to climb off: at the root it goes nowhere, and in a
# relative path it is kept, since the package may still be re-rooted under it
def up.root(abs: Bool) -> List<&2, String>:
  match abs:
    case True{}:
      []
    case False{}:
      [".."]

# a climb past a component that is itself a climb keeps both
def up.back(same: Bool, head: String, rest: List<&2, String>) -> List<&2, String>:
  match same:
    case True{}:
      ".." <> (head <> rest)
    case False{}:
      rest

# a climb against what has been kept: it cancels the last real component
def up.go(+head: String, rest: List<&2, String>) -> List<&2, String>:
  up.back(String.eq(head, ".."), head, rest)

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
def norm.go(st: Walk, comp: Comp) -> Walk:
  Walk{abs, out} = st
  match comp:
    case CSkip{}:
      Walk{abs, out}
    case CUp{}:
      up.step(abs, out)
    case CName{s}:
      Walk{abs, s <> out}

# one component against the state
def norm.step(st: Walk, part: String) -> Walk:
  norm.go(st, comp_of(part))

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

# the walk one component at a time. Base's `List.foldl` applies an erased
# function parameter, which Bend's termination check cannot see through, so
# every def reaching it is reported as relying on unsafe code; a walk written
# out is structural and costs nothing.
def norm.walk(cs: List<&2, String>, st: Walk) -> Walk:
  match cs:
    case []:
      st
    case h <> t:
      norm.walk(t, norm.step(st, h))

# a path with `.` and an inner `..` resolved by text. A leading `..` survives,
# because a module reached through one re-roots the package rather than
# escaping it.
def norm(+path: String) -> String:
  norm.fin(norm.walk(String.split(path, '/'), Walk{String.starts_with(path, "/"), []}))

# the component carried so far, kept when nothing follows it. The list is the
# first argument because that is the one the walk shrinks.
def base.go(ps: List<&2, String>, +last: String) -> String:
  match ps:
    case []:
      last
    case +h2 <> t:
      base.go(t, h2)

# the last component of a path
def base.last(ps: List<&2, String>) -> String:
  match ps:
    case []:
      ""
    case +h <> t:
      base.go(t, h)

# the last component of a path
def base(path: String) -> String:
  base.last(String.split(path, '/'))

# the path with its last component climbed back off
def dir(+path: String) -> String:
  norm(path ++ "/..")

# the path before it is normalised: the second alone when there is no
# directory to take it relative to, the two spliced otherwise. Split out so
# that `norm` runs once. Under a `Bool.pick` both arms were built, so every
# join paid two full component walks and one concatenation it threw away.
def join.at(bare: Bool, left: String, right: String) -> String:
  match bare:
    case True{}:
      right
    case False{}:
      left ++ "/" ++ right

# a path taken relative to a directory. An empty directory means the path is
# already where it should be, and never that it starts at the root.
def join(+left: String, +right: String) -> String:
  norm(join.at(String.is_empty(left), left, right))

# the last `n` components of a path
def tail(path: String, count: Nat) -> String:
  String.join(List.reverse(&2, String,
    List.take(&2, String, List.reverse(&2, String, String.split(path, '/')), count)), "/")

# whether a component is a climb
def up.is(part: String) -> Bool:
  String.eq(part, "..")

# the climbs among components counted one at a time. Base's `List.filter`
# applies an erased function parameter, so it falls outside the termination
# check; this count is structural.
def ups.go(ps: List<&2, String>) -> Nat:
  match ps:
    case []:
      0n
    case +h <> t:
      Nat.add(Bool.pick(Nat, up.is(h), 1n, 0n), ups.go(t))

# how many components of a path are climbs
def ups(path: String) -> Nat:
  ups.go(String.split(path, '/'))

# a module path without its `.bend`, which is how bend names the module
def unbend(+path: String) -> String:
  Bool.pick(String, String.ends_with(path, ".bend"),
    String.take(path, Nat.sub(String.length(path), 5n)), path)

# the path with `n` of its components climbed back off, which is where a
# package re-roots when a module of it was reached through that many `..`
def climb(count: Nat, path: String) -> String:
  match count:
    case 0n:
      norm(path)
    case 1n+q:
      climb(q, dir(path))

# an absolute path, or a `git@` URL, as it is, or a relative path taken from
# `here`
def anchor.path(kept: Bool, +here: String, +path: String) -> String:
  match kept:
    case True{}:
      path
    case False{}:
      join(here, path)

# a URL as it is, or a path
def anchor.at(url: Bool, +here: String, +path: String) -> String:
  match url:
    case True{}:
      path
    case False{}:
      anchor.path(Bool.or(String.starts_with(path, "/"),
        String.starts_with(path, "git@")), here, path)

# a source as the directory `here` reads it. The ledger keeps a local path
# relative to the project, the way it was given, and git reads a relative path
# from somewhere else, so every git command is handed this instead. A URL is
# the same wherever it is read from.
def anchor(+here: String, +path: String) -> String:
  anchor.at(String.contains(path, "://"), here, path)

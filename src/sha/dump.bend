# sha/dump: a directory read off the disk and handed to sha/nar, which builds
# its NAR and names it. The listing is one `find`, run through snap's foreign
# effect, and every regular file is then read. This half lives apart from
# sha/nar because bend 2.0.32 fails a proof whose imports reach foreign code,
# so a law may import sha/nar but never this.
import Base
import 0xead4c7939c9eaca8d47da53b4496b731/main.bend as R
import ../io/file.bend as F
import ./nar.bend as Nar

# a command's output as it printed it, or the walk stopped with why it failed
def said(ok: Bool, +why: String, +text: String) -> IO(String):
  match ok:
    case False{}:
      IO.die(String, 1, "ez: nar hash: " ++ why ++ text)
    case True{}:
      IO.pure(String, text)

# what a program printed, with the status line in front of it taken off and
# nothing else touched
def printed.at(ends: Bool, tail: String, rest: Unit -> String) -> String:
  match ends:
    case True{}:
      tail
    case False{}:
      rest(Unit{})

# the output after its first newline
def printed(out: String) -> String:
  match out:
    case SNil{}:
      ""
    case SCon{c, +t}:
      printed.at(Char.is_eq(c, '\n'), t, _u => printed(t))

# a path of the tree, as the file effect is to open it
def under.top(+top: String, +at: String) -> String:
  Bool.pick(String, String.is_empty(at), top, top ++ "/" ++ at)

def file.got(got: Maybe<&2, String>, +path: String) -> IO(String):
  match got:
    case None{}:
      IO.die(String, 1, "ez: nar hash: " ++ path ++ ": unreadable")
    case Some{s}:
      IO.pure(String, s)

# a regular file's text, by its path from the top
def file.of(+path: String) -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- F.read(path)
    file.got(m, path)

# a path of the listing with what the NAR needs of it: a file's text read, a
# symlink's target as the listing printed it
def ent.other(
  known: Bool,
  +kind: String,
  +name: String,
  +at: String,
  +target: String,
  +path: String
) -> IO(Nar.Ent):
  match known:
    case True{}:
      IO.pure(Nar.Ent, Nar.Ent{kind, False{}, name, at, target})
    case False{}:
      IO.die(Nar.Ent, 1, "ez: nar hash: " ++ path ++ ": not a file, directory, or symlink")

# a regular file's text read, or anything else as the listing gave it
def ent.read(
  file: Bool,
  +kind: String,
  +mode: String,
  +name: String,
  +at: String,
  +target: String,
  +path: String
) -> IO(Nar.Ent):
  match file:
    case True{}:
      do IO<Nar.Ent>:
        body : String <- file.of(path)
        return Nar.Ent{kind, Nar.owner.exec(mode), name, at, body}
    case False{}:
      ent.other(Bool.or(String.eq(kind, "d"), String.eq(kind, "l")), kind, name, at,
        target, path)

# one path of the listing, read
def ent.of(+top: String, row: Nar.Row) -> IO(Nar.Ent):
  Nar.Row{+kind, +mode, +name, +at, +target} = row
  ent.read(String.eq(kind, "f"), kind, mode, name, at, target, under.top(top, at))

# every path of the listing, read
def ents(+top: String, rs: List<&2, Nar.Row>) -> IO(List<&2, Nar.Ent>):
  match rs:
    case []:
      IO.pure(List<&2, Nar.Ent>, [])
    case +h <> t:
      do IO<List<&2, Nar.Ent>>:
        e : Nar.Ent <- ent.of(top, h)
        rest : List<&2, Nar.Ent> <- ents(top, t)
        return e <> rest

# the tree's node, or the walk stopped when the listing made none
def built(got: Maybe<&2, String>, +path: String) -> IO(String):
  match got:
    case None{}:
      IO.die(String, 1, "ez: nar hash: " ++ path ++ ": the listing does not make a tree")
    case Some{node}:
      IO.pure(String, node)

# the NAR serial of one path
def dump(+path: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(Nar.listing.argv(path))
    text : String <- said(R.ok(out), path ++ ": ", printed(out))
    es : List<&2, Nar.Ent> <- ents(path, Nar.rows(Nar.cut(text)))
    built(Nar.tree(es), path)

# the SRI narHash of a path, the same string `nix hash path --sri` prints
def path(+work: String) -> IO(String):
  do IO<String>:
    node : String <- dump(work)
    return Nar.sri(Nar.archive(node))

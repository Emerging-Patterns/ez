# sha/nar: the SRI `nix hash path --sri` would give for a directory, computed
# without nix. A NAR is the tree as length-prefixed strings; its sha256, in
# SRI form, is what fetchgit records as narHash.
#
# The tree is read in one listing, then every regular file's text, and the
# NAR is built from what was read by a pure, fuelled state machine: each step
# places one path or closes one directory, the way lock/resolve and pkg/walk
# carry on, since two Bend defs may not call each other. What the NAR holds
# of a path is what nix's dumper takes: the owner's exec bit of the mode,
# every name and link target as it is, and a file's bytes.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../pkg/pkg.bend as K
import ../sha/sha.bend as Sha

# A directory child is a `K.File`: its name in `at` and the NAR serial of its
# node in `sum`. That is a package file's shape, a name and the text that
# stands for it, so the walk sorts children with the same `K.file.sort` a
# package sorts its files with, and what is proved of that sort is proved of
# the NAR.

# one byte as a character. NAR is a byte stream held in a Bend string.
def byte(+code: U32) -> Char:
  Chr{(code .&. 255 : U32)}

def nat.byte(+value: Nat) -> Char:
  byte(U32.from_nat(Nat.mod(value, 256n)))

def le64.go(width: Nat, +value: Nat) -> String:
  match width:
    case 0n:
      ""
    case 1n+f:
      SCon{nat.byte(value), le64.go(f, Nat.div(value, 256n))}

# a length as NAR writes it: eight bytes, little-endian
def le64(+value: Nat) -> String:
  le64.go(8n, value)

# that many NUL bytes, the padding after a string
def zeros(count: Nat) -> String:
  match count:
    case 0n:
      ""
    case 1n+p:
      SCon{Chr{0}, zeros(p)}

def pad.of(+len: Nat) -> Nat:
  Nat.mod(Nat.sub(8n, Nat.mod(len, 8n)), 8n)

# one NAR string: its length, its bytes, then zeros up to a multiple of eight
def str(+text: String) -> String:
  +n = String.length(text)
  le64(n) ++ text ++ zeros(pad.of(n))

def exec.fields(ex: Bool) -> String:
  match ex:
    case False{}:
      ""
    case True{}:
      str("executable") ++ str("")

# a regular file's node, marked executable when it is
def regular(ex: Bool, +contents: String) -> String:
  str("(") ++ str("type") ++ str("regular") ++ exec.fields(ex)
    ++ str("contents") ++ str(Sha.utf8(contents)) ++ str(")")

# a symlink's node
def symlink(+target: String) -> String:
  str("(") ++ str("type") ++ str("symlink") ++ str("target")
    ++ str(Sha.utf8(target)) ++ str(")")

# one directory entry: its name and its node
def entry(+ent: K.File) -> String:
  K.File{name, node} = ent
  str("entry") ++ str("(") ++ str("name") ++ str(Sha.utf8(name))
    ++ str("node") ++ node ++ str(")")

# a directory's entries, in the order given
def entries(es: List<&2, K.File>) -> String:
  match es:
    case []:
      ""
    case h <> t:
      entry(h) ++ entries(t)

# a directory's node, its entries in the order given
def directory(es: List<&2, K.File>) -> String:
  str("(") ++ str("type") ++ str("directory") ++ entries(es) ++ str(")")

# a directory's node as NAR writes it: its entries sorted by name, whatever
# order they were listed in. `String.is_le` is codepoint order, which is nix's
# byte order for the UTF-8 of valid names. Every directory the walk serializes
# goes through here, so the order `find` printed its names in never reaches
# the NAR.
def dir(es: List<&2, K.File>) -> String:
  directory(K.file.sort(es))

# a whole NAR: the magic, then the root node
def archive(+node: String) -> String:
  str("nix-archive-1") ++ node

def b64.digit.plus(plus: Bool) -> Char:
  match plus:
    case True{}:
      '+'
    case False{}:
      '/'

def b64.digit.lt62(small: Bool, +index: U32) -> Char:
  match small:
    case True{}:
      Chr{U32.add(48, U32.sub(index, 52))}
    case False{}:
      b64.digit.plus(U32.is_eq(index, 62))

def b64.digit.lt52(small: Bool, +index: U32) -> Char:
  match small:
    case True{}:
      Chr{U32.add(97, U32.sub(index, 26))}
    case False{}:
      b64.digit.lt62(U32.is_lt(index, 62), index)

def b64.digit.lt26(small: Bool, +index: U32) -> Char:
  match small:
    case True{}:
      Chr{U32.add(65, index)}
    case False{}:
      b64.digit.lt52(U32.is_lt(index, 52), index)

def b64.digit(+index: U32) -> Char:
  b64.digit.lt26(U32.is_lt(index, 26), index)

def b64.triple(+first: U32, +second: U32, +third: U32) -> String:
  +n = (U32.shln(first, 16n) .|. U32.shln(second, 8n) .|. third : U32)
  SCon{b64.digit(U32.shrn(n, 18n)),
    SCon{b64.digit((U32.shrn(n, 12n) .&. 63 : U32)),
      SCon{b64.digit((U32.shrn(n, 6n) .&. 63 : U32)),
        SCon{b64.digit((n .&. 63 : U32)), SNil{}}}}}

def b64.one(+first: U32) -> String:
  SCon{b64.digit(U32.shrn(first, 2n)),
    SCon{b64.digit(U32.shln((first .&. 3 : U32), 4n)),
      SCon{'=', SCon{'=', SNil{}}}}}

def b64.two(+first: U32, +second: U32) -> String:
  +n = (U32.shln(first, 8n) .|. second : U32)
  SCon{b64.digit(U32.shrn(n, 10n)),
    SCon{b64.digit((U32.shrn(n, 4n) .&. 63 : U32)),
      SCon{b64.digit(U32.shln((n .&. 15 : U32), 2n)),
        SCon{'=', SNil{}}}}}

# standard base64, padded with `=`
def b64(text: String) -> String:
  match text:
    case SNil{}:
      ""
    case SCon{a, SNil{}}:
      b64.one(Char.to_u32(a))
    case SCon{a, SCon{b, SNil{}}}:
      b64.two(Char.to_u32(a), Char.to_u32(b))
    case SCon{a, SCon{b, SCon{c, t}}}:
      b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c)) ++ b64(t)

def hex.val.upper(is_upper: Bool, +code: U32) -> U32:
  match is_upper:
    case True{}:
      U32.sub(code, 55)
    case False{}:
      0

def hex.val.lower(is_lower: Bool, +code: U32) -> U32:
  match is_lower:
    case True{}:
      U32.sub(code, 87)
    case False{}:
      hex.val.upper(Bool.and(U32.is_ge(code, 65), U32.is_le(code, 70)), code)

def hex.val.digit(is_digit: Bool, +code: U32) -> U32:
  match is_digit:
    case True{}:
      U32.sub(code, 48)
    case False{}:
      hex.val.lower(Bool.and(U32.is_ge(code, 97), U32.is_le(code, 102)), code)

def hex.val(+ch: Char) -> U32:
  +u = Char.to_u32(ch)
  hex.val.digit(Bool.and(U32.is_ge(u, 48), U32.is_le(u, 57)), u)

def hex.bytes(text: String) -> String:
  match text:
    case SNil{}:
      ""
    case SCon{_a, SNil{}}:
      ""
    case SCon{a, SCon{b, t}}:
      SCon{byte((U32.shln(hex.val(a), 4n) + hex.val(b) : U32)), hex.bytes(t)}

def sri.hex(+hex: String) -> String:
  "sha256-" ++ b64(hex.bytes(hex))

# the SRI of some bytes: `sha256-` and the base64 of their digest
def sri(+bytes: String) -> String:
  sri.hex(Sha.raw(bytes))

# the node of an empty directory
def empty() -> String:
  dir([])


# ---------------------------------------------------------------------------
# the listing
#
# The tree is listed once, by one `find` from its top, and every field of
# every path is ended by a NUL, the one byte no name or target can hold. So a
# name is read as it is, a space at either end and a newline inside it
# included, and no field is ever trimmed. The paths inside the tree are never
# handed to a program as arguments, since the process effect separates
# arguments by newlines; only the top is, and a file's text is read by its
# path through the file effect, which takes any name.

# the NUL that ends every field of the listing
def nul() -> Char:
  Chr{0}

# a char put in front of the first field, which a text that does not end with
# a NUL leaves open
def push(+ch: Char, fs: List<&2, String>) -> List<&2, String>:
  match fs:
    case []:
      [SCon{ch, SNil{}}]
    case h <> t:
      SCon{ch, h} <> t

# one char of the listing read: a NUL ends a field, any other char is the
# next of the field it is in
def cut.at(ends: Bool, +ch: Char, fs: List<&2, String>) -> List<&2, String>:
  match ends:
    case True{}:
      "" <> fs
    case False{}:
      push(ch, fs)

# the fields of a listing, each ended by a NUL, exactly as they were printed
def cut(text: String) -> List<&2, String>:
  match text:
    case SNil{}:
      []
    case SCon{+c, t}:
      cut.at(Char.is_eq(c, nul()), c, cut(t))

# whether a text holds no NUL, as no name and no link target can
def clean(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{c, t}:
      +rest = clean(t)
      Bool.and(Bool.not(Char.is_eq(c, nul())), rest)

# fields as the listing prints them, each ended by a NUL
def joined(fs: List<&2, String>) -> String:
  match fs:
    case []:
      ""
    case h <> t:
      String.append(h, SCon{nul(), joined(t)})

# whether every field holds no NUL
def clean.all(fs: List<&2, String>) -> Bool:
  match fs:
    case []:
      True{}
    case h <> t:
      +rest = clean.all(t)
      Bool.and(clean(h), rest)

# whether a file's owner may execute it, from the mode `find` prints as
# `%M`, `-rwxr-xr-x`: the fourth character is `x`, or `s` when the setuid
# bit is set as well. This is the mode bit nix's NAR dumper reads
# (`S_IXUSR`), not an access check, so a file the owner may not execute is
# not executable whoever weighs it.
def owner.exec(mode: String) -> Bool:
  match mode:
    case SCon{_t, SCon{_r, SCon{_w, SCon{+x, _rest}}}}:
      Bool.or(Char.is_eq(x, 'x'), Char.is_eq(x, 's'))
    case _:
      False{}

# one path of the listing: its type as `%y` gives it (`d`, `f`, `l`), its
# mode (`%M`), its name (`%f`), its path from the top (`%P`) and a symlink's
# target (`%l`)
type Row is Data:
  Row{kind: String, mode: String, name: String, at: String, target: String}

# the listing's fields, five to a path. A path the listing cut short is not
# read.
def rows(fs: List<&2, String>) -> List<&2, Row>:
  match fs:
    case Con{y, Con{m, Con{f, Con{p, Con{l, rest}}}}}:
      Row{y, m, f, p, l} <> rows(rest)
    case _:
      []

# what `find` is asked to print of every path under `top`, the top first,
# each field ended by a NUL. `find` lists a directory before what is in it
# and all of it before the next entry, which is the order `build` reads.
def listing.argv(+top: String) -> List<&2, String>:
  ["find", top, "-printf", "%y\\0%M\\0%f\\0%P\\0%l\\0"]

# ---------------------------------------------------------------------------
# the tree

# one path of the tree with what the NAR holds of it: a file's text, or a
# symlink's target, as `body`
type Ent is Data:
  Ent{kind: String, exec: Bool, name: String, at: String, body: String}

# a directory still open: its path from the top, its name, and the entries
# found in it so far
type Frame is Data:
  Frame{at: String, name: String, kids: List<&2, K.File>}

# where the build stands: the paths still to place, the directory they are
# being placed in, and the directories around it
type State is Data:
  State{es: List<&2, Ent>, top: Frame, up: List<&2, Frame>}

# a step of the build: another state, or the finished node of the top
type Move is Data:
  Next{st: State}
  Done{node: String}

def leaf.of(link: Bool, ex: Bool, +body: String) -> String:
  match link:
    case True{}:
      symlink(body)
    case False{}:
      regular(ex, body)

# a file's or a symlink's node
def leaf(entry: Ent) -> String:
  Ent{+kind, ex, _name, _at, body} = entry
  leaf.of(String.eq(kind, "l"), ex, body)

# the path of an entry named `name` inside the directory at `at`
def under(+at: String, +name: String) -> String:
  Bool.pick(String, String.is_empty(at), name, at ++ "/" ++ name)

# the directory on top finished: its node is an entry of the one around it,
# or the whole tree when there is none
def close(top: Frame, up: List<&2, Frame>, es: List<&2, Ent>) -> Move:
  Frame{_at, +name, kids} = top
  match up:
    case []:
      Done{dir(kids)}
    case Frame{pat, pname, pkids} <> rest:
      Next{State{es, Frame{pat, pname, K.File{name, dir(kids)} <> pkids}, rest}}

# an entry's type, name and path, and an open directory's path
def ent.kind(entry: Ent) -> String:
  Ent{kind, _ex, _name, _at, _body} = entry
  kind

# an entry's name
def ent.name(entry: Ent) -> String:
  Ent{_kind, _ex, name, _at, _body} = entry
  name

# an entry's path from the top
def ent.at(entry: Ent) -> String:
  Ent{_kind, _ex, _name, at, _body} = entry
  at

# an open directory's path from the top
def frame.at(frame: Frame) -> String:
  Frame{at, _name, _kids} = frame
  at

# a path inside the directory on top: a directory is opened, anything else
# is an entry of it, with its leaf's node
def place(
  is_dir: Bool,
  +name: String,
  +at: String,
  +node: String,
  more: List<&2, Ent>,
  top: Frame,
  up: List<&2, Frame>
) -> Move:
  match is_dir:
    case True{}:
      Next{State{more, Frame{at, name, []}, top <> up}}
    case False{}:
      Frame{a, n, ks} = top
      Next{State{more, Frame{a, n, K.File{name, node} <> ks}, up}}

# the next path: placed when it is inside the directory on top, which closes
# otherwise
def step.ent(
  inside: Bool,
  +entry: Ent,
  more: List<&2, Ent>,
  top: Frame,
  up: List<&2, Frame>
) -> Move:
  match inside:
    case True{}:
      place(String.eq(ent.kind(entry), "d"), ent.name(entry), ent.at(entry), leaf(entry), more, top, up)
    case False{}:
      close(top, up, entry <> more)

# one step of the build
def step(st: State) -> Move:
  State{es, +top, up} = st
  match es:
    case []:
      close(top, up, [])
    case +e <> t:
      step.ent(String.eq(ent.at(e), under(frame.at(top), ent.name(e))), e, t, top, up)

# the build, under fuel
def build.go(fuel: Nat, mv: Move) -> Maybe<&2, String>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match mv:
        case Next{st}:
          build.go(f, step(st))
        case Done{node}:
          Some{node}

# the node of a directory, from its paths in the order `find` lists them. Each
# step places a path or closes a directory, and each directory is closed
# once, so twice the paths and two more is fuel enough.
def build(+es: List<&2, Ent>) -> Maybe<&2, String>:
  +n = List.length(&2, Ent, es)
  build.go(Nat.add(Nat.add(n, n), 2n), Next{State{es, Frame{"", "", []}, []}})

# the node of the whole tree, from its listing with the top first: a
# directory is built, a file or a symlink is a leaf
def tree.top(is_dir: Bool, top: Ent, more: List<&2, Ent>) -> Maybe<&2, String>:
  match is_dir:
    case True{}:
      build(more)
    case False{}:
      Some{leaf(top)}

# the node of the whole tree, or none for an empty listing
def tree(es: List<&2, Ent>) -> Maybe<&2, String>:
  match es:
    case []:
      None{}
    case Ent{+kind, ex, name, at, body} <> t:
      tree.top(String.eq(kind, "d"), Ent{kind, ex, name, at, body}, t)

# ---------------------------------------------------------------------------
# reading it

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
) -> IO(Ent):
  match known:
    case True{}:
      IO.pure(Ent, Ent{kind, False{}, name, at, target})
    case False{}:
      IO.die(Ent, 1, "ez: nar hash: " ++ path ++ ": not a file, directory, or symlink")

# a regular file's text read, or anything else as the listing gave it
def ent.read(
  file: Bool,
  +kind: String,
  +mode: String,
  +name: String,
  +at: String,
  +target: String,
  +path: String
) -> IO(Ent):
  match file:
    case True{}:
      do IO<Ent>:
        body : String <- file.of(path)
        return Ent{kind, owner.exec(mode), name, at, body}
    case False{}:
      ent.other(Bool.or(String.eq(kind, "d"), String.eq(kind, "l")), kind, name, at,
        target, path)

# one path of the listing, read
def ent.of(+top: String, row: Row) -> IO(Ent):
  Row{+kind, +mode, +name, +at, +target} = row
  ent.read(String.eq(kind, "f"), kind, mode, name, at, target, under.top(top, at))


# every path of the listing, read
def ents(+top: String, rs: List<&2, Row>) -> IO(List<&2, Ent>):
  match rs:
    case []:
      IO.pure(List<&2, Ent>, [])
    case +h <> t:
      do IO<List<&2, Ent>>:
        e : Ent <- ent.of(top, h)
        rest : List<&2, Ent> <- ents(top, t)
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
    +out : String <- R.exec(listing.argv(path))
    text : String <- said(R.ok(out), path ++ ": ", printed(out))
    es : List<&2, Ent> <- ents(path, rows(cut(text)))
    built(tree(es), path)

# the SRI narHash of a path, the same string `nix hash path --sri` prints
def path(+work: String) -> IO(String):
  do IO<String>:
    node : String <- dump(work)
    return sri(archive(node))

# sha/nar: the SRI `nix hash path --sri` would give for a directory, computed
# without nix. A NAR is the tree as length-prefixed strings; its sha256, in
# SRI form, is what fetchgit records as narHash.
#
# The walk is a fuelled state machine: each step does one filesystem probe and
# at most one recursive call, the way lock/resolve and pkg/walk carry on, since
# two Bend defs may not call each other and a linear continuation may be used
# only once.
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

# what to do with a node's serial once it is known
type After is Data:
  Done{}
  ChildOf{here: String, name: String, rest: List<&2, String>,
    acc: List<&2, K.File>, parent: After}

# one step of the walk
type Goal is Data:
  Load{at: String, k: After}
  FinishDir{kids: List<&2, K.File>, k: After}

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

# a command's output, trimmed, or the walk stopped with why it failed
def said(ok: Bool, +why: String, +text: String) -> IO(String):
  match ok:
    case False{}:
      IO.die(String, 1, "ez: nar hash: " ++ why ++ text)
    case True{}:
      IO.pure(String, String.trim(text))

# the lines that are not empty
def nonblank(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case []:
      []
    case Con{+h, t}:
      +more = nonblank(t)
      Bool.pick(List<&2, String>, String.is_empty(h), more, h <> more)

# the names in a directory, in the order `find` lists them, without `.` and
# `..`. `dir` puts them in NAR order once they are loaded.
def names(+path: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["find", path, "-mindepth", "1", "-maxdepth", "1",
      "-printf", "%f\\n"])
    text : String <- said(R.ok(out), path ++ ": ", R.text(out))
    return nonblank(String.lines(text))

def link.of(+path: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["readlink", "-n", path])
    said(R.ok(out), path ++ ": ", R.text(out))

def file.got(got: Maybe<&2, String>, path: String) -> IO(String):
  match got:
    case None{}:
      IO.die(String, 1, "ez: nar hash: " ++ path ++ ": unreadable")
    case Some{s}:
      IO.pure(String, s)

def file.of(+path: String) -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- F.read(path)
    file.got(m, path)

def exec.of(+path: String) -> IO(Bool):
  do IO<Bool>:
    +out : String <- R.exec(["test", "-x", path])
    return R.ok(out)

# apply a finished serial to its continuation; uses `go` at most once
def cont.next(
  +here: String,
  rest: List<&2, String>,
  acc: List<&2, K.File>,
  parent: After,
  go: Goal -> IO(String)
) -> IO(String):
  match rest:
    case []:
      go(FinishDir{acc, parent})
    case +h <> t:
      go(Load{here ++ "/" ++ h, ChildOf{here, h, t, acc, parent}})

def cont.rest(
  empty: Bool,
  +here: String,
  rest: List<&2, String>,
  +acc: List<&2, K.File>,
  parent: After,
  go: Goal -> IO(String)
) -> IO(String):
  match empty:
    case True{}:
      go(FinishDir{acc, parent})
    case False{}:
      cont.next(here, rest, acc, parent, go)

def cont.apply(+ser: String, after: After, go: Goal -> IO(String)) -> IO(String):
  match after:
    case Done{}:
      IO.pure(String, ser)
    case ChildOf{+here, +name, +rest, acc, parent}:
      cont.rest(List.is_empty(&2, String, rest), here, rest,
        K.File{name, ser} <> acc, parent, go)

# an empty directory under a continuation
def load.dir.empty(after: After, go: Goal -> IO(String)) -> IO(String):
  go(FinishDir{[], after})

# a non-empty directory: start with its first child
def load.dir.kids(+path: String, ns: List<&2, String>, after: After, go: Goal -> IO(String)) -> IO(String):
  match ns:
    case []:
      load.dir.empty(after, go)
    case +h <> t:
      go(Load{path ++ "/" ++ h, ChildOf{path, h, t, [], after}})

# a directory after its child names are known
def load.dir(+path: String, ns: List<&2, String>, after: After, go: Goal -> IO(String)) -> IO(String):
  load.dir.kids(path, ns, after, go)

# a regular file's serial handed to its continuation
def load.file(+path: String, after: After, go: Goal -> IO(String)) -> IO(String):
  do IO<String>:
    ex : Bool <- exec.of(path)
    body : String <- file.of(path)
    cont.apply(regular(ex, body), after, go)

# a symlink's serial handed to its continuation
def load.link(+path: String, after: After, go: Goal -> IO(String)) -> IO(String):
  do IO<String>:
    t : String <- link.of(path)
    cont.apply(symlink(t), after, go)

# open a directory and continue
def load.open(+path: String, after: After, go: Goal -> IO(String)) -> IO(String):
  do IO<String>:
    ns : List<&2, String> <- names(path)
    load.dir(path, ns, after, go)

def load.file.only(file: Bool, +path: String, after: After, go: Goal -> IO(String)) -> IO(String):
  match file:
    case True{}:
      load.file(path, after, go)
    case False{}:
      IO.die(String, 1, "ez: nar hash: " ++ path ++ ": not a file, directory, or symlink")

# non-symlink
def load.plain(is_dir: Bool, file: Bool, +path: String, after: After, go: Goal -> IO(String)) -> IO(String):
  match is_dir:
    case True{}:
      load.open(path, after, go)
    case False{}:
      load.file.only(file, path, after, go)

# probes answered for a Load goal
def load.kind(link: Bool, is_dir: Bool, file: Bool, +path: String, after: After, go: Goal -> IO(String)) -> IO(String):
  match link:
    case True{}:
      load.link(path, after, go)
    case False{}:
      load.plain(is_dir, file, path, after, go)

# one Load goal after probes
def load.at(+path: String, after: After, go: Goal -> IO(String)) -> IO(String):
  do IO<String>:
    +l : String <- R.exec(["test", "-L", path])
    +d : String <- R.exec(["test", "-d", path])
    +r : String <- R.exec(["test", "-f", path])
    load.kind(R.ok(l), R.ok(d), R.ok(r), path, after, go)

# FinishDir: the directory's serial, its loaded children sorted, under its
# continuation
def load.finish(kids: List<&2, K.File>, after: After, go: Goal -> IO(String)) -> IO(String):
  cont.apply(dir(kids), after, go)

# one step; `go` continues with decreased fuel
def load.step(goal: Goal, go: Goal -> IO(String)) -> IO(String):
  match goal:
    case Load{+at, k}:
      load.at(at, k, go)
    case FinishDir{kids, k}:
      load.finish(kids, k, go)

# the fuelled walk
def load.go(fuel: Nat, goal: Goal) -> IO(String):
  match fuel:
    case 0n:
      IO.die(String, 1, "ez: nar hash: tree too deep")
    case 1n+f:
      +n = f
      load.step(goal, g2 => load.go(n, g2))

# the NAR serial of one path
def dump(+path: String) -> IO(String):
  load.go(U32.to_nat(100000), Load{path, Done{}})

# the SRI narHash of a path, the same string `nix hash path --sri` prints
def path(+work: String) -> IO(String):
  do IO<String>:
    node : String <- dump(work)
    return sri(archive(node))

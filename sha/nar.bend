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
import ./sha.bend as Sha

# one directory child: its name, and the NAR serial of its node
type Ent is Data:
  Ent{name: String, node: String}

# what to do with a node's serial once it is known
type After is Data:
  Done{}
  ChildOf{dir: String, name: String, rest: List<&2, String>,
    acc: List<&2, Ent>, parent: After}

# one step of the walk
type Goal is Data:
  Load{at: String, k: After}
  FinishDir{kids: List<&2, Ent>, k: After}

# one byte as a character. NAR is a byte stream held in a Bend string.
def byte(+x: U32) -> Char:
  Chr{(x .&. 255 : U32)}

def nat.byte(+n: Nat) -> Char:
  byte(U32.from_nat(Nat.mod(n, 256n)))

def le64.go(width: Nat, +n: Nat) -> String:
  match width:
    case 0n:
      ""
    case 1n+f:
      SCon{nat.byte(n), le64.go(f, Nat.div(n, 256n))}

# a length as NAR writes it: eight bytes, little-endian
def le64(+n: Nat) -> String:
  le64.go(8n, n)

# that many NUL bytes, the padding after a string
def zeros(n: Nat) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      SCon{Chr{0}, zeros(p)}

def pad.of(+n: Nat) -> Nat:
  Nat.mod(Nat.sub(8n, Nat.mod(n, 8n)), 8n)

# one NAR string: its length, its bytes, then zeros up to a multiple of eight
def str(+s: String) -> String:
  +n = String.length(s)
  le64(n) ++ s ++ zeros(pad.of(n))

def utf8.1(+u: U32) -> String:
  SCon{byte(u), SNil{}}

def utf8.2(+u: U32) -> String:
  SCon{byte((192 .|. U32.shrn(u, 6n) : U32)),
    SCon{byte((128 .|. (u .&. 63 : U32) : U32)), SNil{}}}

def utf8.3(+u: U32) -> String:
  SCon{byte((224 .|. U32.shrn(u, 12n) : U32)),
    SCon{byte((128 .|. (U32.shrn(u, 6n) .&. 63 : U32) : U32)),
      SCon{byte((128 .|. (u .&. 63 : U32) : U32)), SNil{}}}}

def utf8.4(+u: U32) -> String:
  SCon{byte((240 .|. U32.shrn(u, 18n) : U32)),
    SCon{byte((128 .|. (U32.shrn(u, 12n) .&. 63 : U32) : U32)),
      SCon{byte((128 .|. (U32.shrn(u, 6n) .&. 63 : U32) : U32)),
        SCon{byte((128 .|. (u .&. 63 : U32) : U32)), SNil{}}}}}

def utf8.put.3(three: Bool, +u: U32) -> String:
  match three:
    case True{}:
      utf8.3(u)
    case False{}:
      utf8.4(u)

def utf8.put.2(two: Bool, +u: U32) -> String:
  match two:
    case True{}:
      utf8.2(u)
    case False{}:
      utf8.put.3(U32.is_lt(u, 65536), u)

def utf8.put.ascii(ascii: Bool, +u: U32) -> String:
  match ascii:
    case True{}:
      utf8.1(u)
    case False{}:
      utf8.put.2(U32.is_lt(u, 2048), u)

def utf8.put(+u: U32) -> String:
  utf8.put.ascii(U32.is_lt(u, 128), u)

# the string's characters encoded as UTF-8, each byte a character
def utf8(+s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{c, t}:
      utf8.put(Char.to_u32(c)) ++ utf8(t)

def exec.fields(ex: Bool) -> String:
  match ex:
    case False{}:
      ""
    case True{}:
      str("executable") ++ str("")

# a regular file's node, marked executable when it is
def regular(ex: Bool, +contents: String) -> String:
  str("(") ++ str("type") ++ str("regular") ++ exec.fields(ex)
    ++ str("contents") ++ str(utf8(contents)) ++ str(")")

# a symlink's node
def symlink(+target: String) -> String:
  str("(") ++ str("type") ++ str("symlink") ++ str("target")
    ++ str(utf8(target)) ++ str(")")

# one directory entry: its name and its node
def entry(+e: Ent) -> String:
  Ent{name, node} = e
  str("entry") ++ str("(") ++ str("name") ++ str(utf8(name))
    ++ str("node") ++ node ++ str(")")

# a directory's entries, in the order given
def entries(es: List<&2, Ent>) -> String:
  match es:
    case []:
      ""
    case h <> t:
      entry(h) ++ entries(t)

# a directory's node
def directory(es: List<&2, Ent>) -> String:
  str("(") ++ str("type") ++ str("directory") ++ entries(es) ++ str(")")

# a whole NAR: the magic, then the root node
def archive(+node: String) -> String:
  str("nix-archive-1") ++ node

def b64.digit.plus(plus: Bool) -> Char:
  match plus:
    case True{}:
      '+'
    case False{}:
      '/'

def b64.digit.lt62(small: Bool, +i: U32) -> Char:
  match small:
    case True{}:
      Chr{U32.add(48, U32.sub(i, 52))}
    case False{}:
      b64.digit.plus(U32.is_eq(i, 62))

def b64.digit.lt52(small: Bool, +i: U32) -> Char:
  match small:
    case True{}:
      Chr{U32.add(97, U32.sub(i, 26))}
    case False{}:
      b64.digit.lt62(U32.is_lt(i, 62), i)

def b64.digit.lt26(small: Bool, +i: U32) -> Char:
  match small:
    case True{}:
      Chr{U32.add(65, i)}
    case False{}:
      b64.digit.lt52(U32.is_lt(i, 52), i)

def b64.digit(+i: U32) -> Char:
  b64.digit.lt26(U32.is_lt(i, 26), i)

def b64.triple(+a: U32, +b: U32, +c: U32) -> String:
  +n = (U32.shln(a, 16n) .|. U32.shln(b, 8n) .|. c : U32)
  SCon{b64.digit(U32.shrn(n, 18n)),
    SCon{b64.digit((U32.shrn(n, 12n) .&. 63 : U32)),
      SCon{b64.digit((U32.shrn(n, 6n) .&. 63 : U32)),
        SCon{b64.digit((n .&. 63 : U32)), SNil{}}}}}

def b64.one(+a: U32) -> String:
  SCon{b64.digit(U32.shrn(a, 2n)),
    SCon{b64.digit(U32.shln((a .&. 3 : U32), 4n)),
      SCon{'=', SCon{'=', SNil{}}}}}

def b64.two(+a: U32, +b: U32) -> String:
  +n = (U32.shln(a, 8n) .|. b : U32)
  SCon{b64.digit(U32.shrn(n, 10n)),
    SCon{b64.digit((U32.shrn(n, 4n) .&. 63 : U32)),
      SCon{b64.digit(U32.shln((n .&. 15 : U32), 2n)),
        SCon{'=', SNil{}}}}}

# standard base64, padded with `=`
def b64(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{a, SNil{}}:
      b64.one(Char.to_u32(a))
    case SCon{a, SCon{b, SNil{}}}:
      b64.two(Char.to_u32(a), Char.to_u32(b))
    case SCon{a, SCon{b, SCon{c, t}}}:
      b64.triple(Char.to_u32(a), Char.to_u32(b), Char.to_u32(c)) ++ b64(t)

def hex.val.upper(is_upper: Bool, +u: U32) -> U32:
  match is_upper:
    case True{}:
      U32.sub(u, 55)
    case False{}:
      0

def hex.val.lower(is_lower: Bool, +u: U32) -> U32:
  match is_lower:
    case True{}:
      U32.sub(u, 87)
    case False{}:
      hex.val.upper(Bool.and(U32.is_ge(u, 65), U32.is_le(u, 70)), u)

def hex.val.digit(is_digit: Bool, +u: U32) -> U32:
  match is_digit:
    case True{}:
      U32.sub(u, 48)
    case False{}:
      hex.val.lower(Bool.and(U32.is_ge(u, 97), U32.is_le(u, 102)), u)

def hex.val(+c: Char) -> U32:
  +u = Char.to_u32(c)
  hex.val.digit(Bool.and(U32.is_ge(u, 48), U32.is_le(u, 57)), u)

def hex.bytes(s: String) -> String:
  match s:
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
  sri.hex(Sha.hex(bytes))

# the node of an empty directory
def empty() -> String:
  directory([])

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

# where one name belongs in a list already sorted. Insertion keeps the
# termination check happy; Base's List.sort does not.
def sort.ins.put(le: Bool, +x: String, h: String, t: List<&2, String>,
  rest: List<&2, String>) -> List<&2, String>:
  match le:
    case True{}:
      x <> (h <> t)
    case False{}:
      h <> rest

def sort.ins(+x: String, ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case []:
      [x]
    case +h <> +t:
      sort.ins.put(String.is_le(x, h), x, h, t, sort.ins(x, t))

# directory entry names in lexicographic order, the order NAR walks them
def sort(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case []:
      []
    case +h <> t:
      sort.ins(h, sort(t))

# the names in a directory, sorted, without `.` and `..`
def names(+path: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["find", path, "-mindepth", "1", "-maxdepth", "1",
      "-printf", "%f\\n"])
    text : String <- said(R.ok(out), path ++ ": ", R.text(out))
    return sort(nonblank(String.lines(text)))

def link.of(+path: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["readlink", "-n", path])
    said(R.ok(out), path ++ ": ", R.text(out))

def file.got(m: Maybe<&2, String>, path: String) -> IO(String):
  match m:
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

def ents.rev.go(es: List<&2, Ent>, acc: List<&2, Ent>) -> List<&2, Ent>:
  match es:
    case []:
      acc
    case h <> t:
      ents.rev.go(t, h <> acc)

def ents.rev(es: List<&2, Ent>) -> List<&2, Ent>:
  ents.rev.go(es, [])

# apply a finished serial to its continuation; uses `go` at most once
def cont.next(+dir: String, rest: List<&2, String>, acc: List<&2, Ent>,
  parent: After, go: Goal -> IO(String)) -> IO(String):
  match rest:
    case []:
      go(FinishDir{ents.rev(acc), parent})
    case +h <> t:
      go(Load{dir ++ "/" ++ h, ChildOf{dir, h, t, acc, parent}})

def cont.rest(empty: Bool, +dir: String, rest: List<&2, String>,
  +acc: List<&2, Ent>, parent: After, go: Goal -> IO(String)) -> IO(String):
  match empty:
    case True{}:
      go(FinishDir{ents.rev(acc), parent})
    case False{}:
      cont.next(dir, rest, acc, parent, go)

def cont.apply(+ser: String, k: After, go: Goal -> IO(String)) -> IO(String):
  match k:
    case Done{}:
      IO.pure(String, ser)
    case ChildOf{+dir, +name, +rest, acc, parent}:
      cont.rest(List.is_empty(&2, String, rest), dir, rest,
        Ent{name, ser} <> acc, parent, go)

# an empty directory under a continuation
def load.dir.empty(k: After, go: Goal -> IO(String)) -> IO(String):
  go(FinishDir{[], k})

# a non-empty directory: start with its first child
def load.dir.kids(+path: String, ns: List<&2, String>, k: After,
  go: Goal -> IO(String)) -> IO(String):
  match ns:
    case []:
      load.dir.empty(k, go)
    case +h <> t:
      go(Load{path ++ "/" ++ h, ChildOf{path, h, t, [], k}})

# a directory after its child names are known
def load.dir(+path: String, ns: List<&2, String>, k: After,
  go: Goal -> IO(String)) -> IO(String):
  load.dir.kids(path, ns, k, go)

# a regular file's serial handed to its continuation
def load.file(+path: String, k: After, go: Goal -> IO(String)) -> IO(String):
  do IO<String>:
    ex : Bool <- exec.of(path)
    body : String <- file.of(path)
    cont.apply(regular(ex, body), k, go)

# a symlink's serial handed to its continuation
def load.link(+path: String, k: After, go: Goal -> IO(String)) -> IO(String):
  do IO<String>:
    t : String <- link.of(path)
    cont.apply(symlink(t), k, go)

# open a directory and continue
def load.open(+path: String, k: After, go: Goal -> IO(String)) -> IO(String):
  do IO<String>:
    ns : List<&2, String> <- names(path)
    load.dir(path, ns, k, go)

def load.file.only(file: Bool, +path: String, k: After,
  go: Goal -> IO(String)) -> IO(String):
  match file:
    case True{}:
      load.file(path, k, go)
    case False{}:
      IO.die(String, 1, "ez: nar hash: " ++ path ++ ": not a file, directory, or symlink")

# non-symlink
def load.plain(is_dir: Bool, file: Bool, +path: String, k: After,
  go: Goal -> IO(String)) -> IO(String):
  match is_dir:
    case True{}:
      load.open(path, k, go)
    case False{}:
      load.file.only(file, path, k, go)

# probes answered for a Load goal
def load.kind(link: Bool, is_dir: Bool, file: Bool, +path: String, k: After,
  go: Goal -> IO(String)) -> IO(String):
  match link:
    case True{}:
      load.link(path, k, go)
    case False{}:
      load.plain(is_dir, file, path, k, go)

# one Load goal after probes
def load.at(+path: String, k: After, go: Goal -> IO(String)) -> IO(String):
  do IO<String>:
    +l : String <- R.exec(["test", "-L", path])
    +d : String <- R.exec(["test", "-d", path])
    +r : String <- R.exec(["test", "-f", path])
    load.kind(R.ok(l), R.ok(d), R.ok(r), path, k, go)

# FinishDir: directory serial under its continuation
def load.finish(kids: List<&2, Ent>, k: After, go: Goal -> IO(String)) -> IO(String):
  cont.apply(directory(kids), k, go)

# one step; `go` continues with decreased fuel
def load.step(g: Goal, go: Goal -> IO(String)) -> IO(String):
  match g:
    case Load{+at, k}:
      load.at(at, k, go)
    case FinishDir{kids, k}:
      load.finish(kids, k, go)

# the fuelled walk
def load.go(fuel: Nat, g: Goal) -> IO(String):
  match fuel:
    case 0n:
      IO.die(String, 1, "ez: nar hash: tree too deep")
    case 1n+f:
      +n = f
      load.step(g, g2 => load.go(n, g2))

# the NAR serial of one path
def dump(+path: String) -> IO(String):
  load.go(U32.to_nat(100000), Load{path, Done{}})

# the SRI narHash of a path, the same string `nix hash path --sri` prints
def path(+work: String) -> IO(String):
  do IO<String>:
    node : String <- dump(work)
    return sri(archive(node))

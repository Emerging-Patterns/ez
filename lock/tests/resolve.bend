# lock: the transitive walk. A project's own files are followed into one
# another, every package they name is resolved, and a package's own imports are
# resolved behind it. The packages here are vendored ones, laid out under a
# BEND_LIB of the test's own, so the walk needs no hub and no network.
import Base
import ../lock.bend as L
import ../../io/file.bend as F
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../../sha/sha.bend as Sha
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../../check/kit.bend as Check

# the three package names the fixture uses
def a() -> String:
  "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"

def b() -> String:
  "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"

def c() -> String:
  "0xcccccccccccccccccccccccccccccccc"

# a package that depends on nothing
def leaf() -> String:
  "import Base\n\n# double the number\ndef double(+x: U32) -> U32:\n  (x * 2 : U32)\n"

# a package that imports another package
def mid() -> String:
  "import Base\nimport " ++ a() ++ "/lib.bend as A\n\n" ++
  "# four times the number\ndef quad(+x: U32) -> U32:\n  A.double(A.double(x))\n"

# the manifest ez writes beside a vendored package
def manifest(+src: String) -> String:
  Sha.hex(src) ++ " lib.bend\n"

# one vendored package under a BEND_LIB
def vendor(+lib: String, +hash: String, +src: String) -> IO(Unit):
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", lib ++ "/" ++ hash])
    _f : Bool <- F.write(lib ++ "/" ++ hash ++ "/lib.bend", src)
    _m : Bool <- F.write(lib ++ "/" ++ hash ++ "/manifest", manifest(src))
    return Unit{}

# what .ez/origins.toml says about one vendored package
def origin(+hash: String) -> String:
  "[origins." ++ T.quote(hash) ++ "]\n" ++
  "kind = \"git\"\nurl = \"https://h/" ++ hash ++ "\"\nrev = \"c0ffee\"\n" ++
  "entry = \"lib.bend\"\nroot = \".\"\nnarHash = \"sha256-zz\"\n\n"

# what ez.toml says about one vendored package. The rev differs from the
# cache's, so which file a rev came from is visible in the answer.
def ledger(+name: String, +hash: String) -> String:
  "\n[deps." ++ name ++ "]\nhash = \"" ++ hash ++ "\"\n" ++
  "git = \"https://h/" ++ hash ++ "\"\nrev = \"beef\"\nroot = \".\"\n" ++
  "narHash = \"sha256-yy\"\nentry = \"lib.bend\"\n"

# the project, its packages, and the two files that say where they came from.
# `b` is in both, with a different rev in each, and `c` is in the ledger alone,
# which is the state a fresh clone is in for every package it has.
def fixture(+d: String) -> IO(Unit):
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", d ++ "/app"])
    vendor(d ++ "/lib", a(), leaf())
    vendor(d ++ "/lib", b(), mid())
    vendor(d ++ "/lib", c(), leaf())
    _o : Bool <- F.write(d ++ "/origins.toml", origin(a()) ++ origin(b()))
    _t : Bool <- F.write(d ++ "/ez.toml",
      "[package]\nname = \"fixture\"\nentry = \"app/main.bend\"\n" ++
      ledger("mid", b()) ++ ledger("leaf", c()))
    _m : Bool <- F.write(d ++ "/app/main.bend",
      "import Base\nimport " ++ b() ++ "/lib.bend as B\nimport ./side.bend as S\n")
    _s : Bool <- F.write(d ++ "/app/side.bend",
      "import Base\nimport " ++ c() ++ "/lib.bend as C\n")
    return Unit{}

# the tables of a lock that was written
def sects(s: String) -> List<&2, T.Sect>:
  T.sects(T.parse(s))

# every package a lock records, by hash
def names(+text: String) -> String:
  String.join(L.hashes(sects(text)), " ")

# the files a lock records for one package
def files(+text: String, hash: String) -> String:
  L.pack.manifest(L.pack_of(sects(text), hash))

def main() -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(["mktemp", "-d"])
    +d : String <- IO.pure(String, String.trim(R.text(out)))
    fixture(d)
    +text : String <- L.lock.at("https://hub.example", d ++ "/ez.toml",
      d ++ "/lib", [d ++ "/app/main.bend"])
    Check.eq_str("a package reached through another file, and one reached through a package",
      names(text), a() ++ " " ++ b() ++ " " ++ c())
    Check.eq_str("a package's files come with the sha256 its manifest named",
      files(text, a()), manifest(leaf()))
    Check.eq_str("a vendored package records the rev it was pinned to",
      L.src.rev(L.pack.src(L.pack_of(sects(text), a()))), "c0ffee")
    _rm : String <- R.exec(["rm", "-rf", d])
    return Unit{}

#|ok a package reached through another file, and one reached through a package
#|ok a package's files come with the sha256 its manifest named
#|ok a vendored package records the rev it was pinned to

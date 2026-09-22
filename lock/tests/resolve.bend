# lock: the transitive walk. A project's own files are followed into one
# another, every package they name is resolved, and a package's own imports are
# resolved behind it. The packages here are vendored ones, laid out under a
# BEND_LIB of the test's own, so the walk needs no hub and no network. Each is
# named by the digest of its manifest, as bend names a package, since a tree
# whose manifest is not its name's is refused.
import Base
import ../lock.bend as L
import ../../io/file.bend as F
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../../sha/sha.bend as Sha
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../../check/kit.bend as Check
import ../../ez/sorted.bend as Sorted

# a package that depends on nothing
def leaf() -> String:
  "import Base\n\n# double the number\ndef double(+x: U32) -> U32:\n  (x * 2 : U32)\n"

# another package that depends on nothing
def other() -> String:
  "import Base\n\n# triple the number\ndef triple(+x: U32) -> U32:\n  (x * 3 : U32)\n"

# the manifest ez writes beside a vendored package
def manifest(+src: String) -> String:
  Sha.hex(src) ++ " lib.bend\n"

# the name a one-file package is published under
def name(+src: String) -> String:
  "0x" ++ String.take(Sha.hex(manifest(src)), 32n)

# the name of the package that depends on nothing
def a() -> String:
  name(leaf())

# a package that imports another package
def mid() -> String:
  "import Base\nimport " ++ a() ++ "/lib.bend as A\n\n" ++
  "# four times the number\ndef quad(+x: U32) -> U32:\n  A.double(A.double(x))\n"

# the names of the other two
def b() -> String:
  name(mid())

def c() -> String:
  name(other())

# one vendored package under a BEND_LIB
def vendor(+lib: String, +hash: String, +src: String) -> IO(Unit):
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", lib ++ "/" ++ hash])
    _f : Bool <- F.write(lib ++ "/" ++ hash ++ "/lib.bend", src)
    _m : Bool <- F.write(lib ++ "/" ++ hash ++ "/manifest", manifest(src))
    return Unit{}

# what ez.toml says about one vendored package
def ledger(+name: String, +hash: String) -> String:
  "\n[deps." ++ name ++ "]\nhash = \"" ++ hash ++ "\"\n" ++
  "git = \"https://h/" ++ hash ++ "\"\nrev = \"beef\"\nroot = \".\"\n" ++
  "narHash = \"sha256-yy\"\nentry = \"lib.bend\"\n"

# the project, its packages, and the ledger that says where they came from.
# A stray `.ez/origins.toml` beside the BEND_LIB says otherwise about `a`, and
# is not read: the ledger is the only record a clone has.
def fixture(+dir: String) -> IO(Unit):
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", dir ++ "/app"])
    vendor(dir ++ "/lib", a(), leaf())
    vendor(dir ++ "/lib", b(), mid())
    vendor(dir ++ "/lib", c(), other())
    _o : Bool <- F.write(dir ++ "/origins.toml",
      "[origins." ++ T.quote(a()) ++ "]\nkind = \"git\"\nurl = \"https://h/x\"\n" ++
      "rev = \"c0ffee\"\nentry = \"lib.bend\"\nroot = \".\"\nnarHash = \"sha256-zz\"\n")
    _t : Bool <- F.write(dir ++ "/ez.toml",
      "[package]\nname = \"fixture\"\nentry = \"app/main.bend\"\n" ++
      ledger("double", a()) ++ ledger("mid", b()) ++ ledger("leaf", c()))
    _m : Bool <- F.write(dir ++ "/app/main.bend",
      "import Base\nimport " ++ b() ++ "/lib.bend as B\nimport ./side.bend as S\n")
    _s : Bool <- F.write(dir ++ "/app/side.bend",
      "import Base\nimport " ++ c() ++ "/lib.bend as C\n")
    return Unit{}

# the tables of a lock that was written
def sects(text: String) -> List<&2, T.Sect>:
  T.sects(T.parse(text))

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
    +text : String <- L.lock.at(d ++ "/ez.toml", d ++ "/lib",
      [d ++ "/app/main.bend"])
    Check.eq_str("a package reached through another file, and one reached through a package",
      names(text), String.join(Sorted.sort([a(), b(), c()]), " "))
    Check.eq_str("a package's files come with the sha256 its manifest named",
      files(text, a()), manifest(leaf()))
    Check.eq_str("a vendored package records the rev the ledger pinned, whatever the cache says",
      L.src.rev(L.pack.src(L.pack_of(sects(text), a()))), "beef")
    Check.eq_str("a ledger that names no hub locks against bend's",
      L.lock.hub(sects(text)), "https://hub.bend-lang.com")
    _rm : String <- R.exec(["rm", "-rf", d])
    return Unit{}

#|ok a package reached through another file, and one reached through a package
#|ok a package's files come with the sha256 its manifest named
#|ok a vendored package records the rev the ledger pinned, whatever the cache says
#|ok a ledger that names no hub locks against bend's

# lock: the lock document, written and read back
import Base
import ../lock.bend as L
import ../../pkg/pkg.bend as K
import ../../manifest/toml.bend as T
import ../../check/kit.bend as Check

# a hub package and a vendored one, the two shapes a lock records
def packs() -> List<&2, L.Pack>:
  [L.Pack{"0xbb", L.Hub{}, [K.File{"src/lib.bend", "ab"}]},
   L.Pack{"0xaa", L.Git{"https://h/r", "c0ffee", "src/lib.bend", ".",
     "sha256-zz", "v1.0"}, [K.File{"lib.bend", "cd"}]}]

# the lock those packages render to
def text() -> String:
  L.render("https://hub.bend-lang.com", "2.0.16", packs())

# the tables of a document that was read
def sects(s: String) -> List<&2, T.Sect>:
  T.sects(T.parse(s))

# a package read back out of a lock, on one line
def shown(+p: L.Pack) -> String:
  L.pack.hash(p) ++ " " ++ L.src.kind(L.pack.src(p)) ++ " " ++
  K.manifest_of(L.pack.files(p))

# every package a lock records, shown
def all(ps: List<&2, L.Pack>) -> String:
  match ps:
    case []:
      ""
    case h <> t:
      shown(h) ++ all(t)

# a .ez/origins.toml, as ez-git writes it
def orig() -> String:
  "[origins.\"0xaa\"]\n" ++
  "kind = \"git\"\n" ++
  "url = \"https://h/r\"\n" ++
  "rev = \"c0ffee\"\n" ++
  "entry = \"src/lib.bend\"\n" ++
  "root = \".\"\n"

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("a lock names its hub and the bend that resolved it",
      L.lock.hub(sects(text())), "https://hub.bend-lang.com")
    Check.eq_str("packages are written in hash order",
      String.join(L.hashes(sects(text())), " "), "0xaa 0xbb")
    Check.eq_str("what was written reads back as what it was",
      all(L.packs(sects(text()))),
      "0xaa git cd lib.bend\n0xbb hub ab src/lib.bend\n")
    Check.eq_str("a vendored package keeps the rev it was pinned to",
      L.src.rev(L.pack.src(L.pack_of(sects(text()), "0xaa"))), "c0ffee")
    Check.eq_str("an origin says where a vendored package came from",
      L.src.url(L.origin(L.origins(sects(orig())), "0xaa")), "https://h/r")
    Check.eq_str("a package nothing vendored comes from the hub",
      L.src.kind(L.origin(L.origins(sects(orig())), "0xzz")), "hub")
    Check.eq_str("an import names the package before its first slash",
      L.spec.hash("0xaabb/src/lib.bend"), "0xaabb")

#|ok a lock names its hub and the bend that resolved it
#|ok packages are written in hash order
#|ok what was written reads back as what it was
#|ok a vendored package keeps the rev it was pinned to
#|ok an origin says where a vendored package came from
#|ok a package nothing vendored comes from the hub
#|ok an import names the package before its first slash

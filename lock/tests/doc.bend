# lock: origins.toml read back. The cache names a package or it does
# not, and that is the only question this file asks.
import Base
import ../lock.bend as L
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../../check/kit.bend as Check

# the tables of a document that was read
def sects(text: String) -> List<&2, T.Sect>:
  T.sects(T.parse(text))

# a .ez/origins.toml, as `git/git.bend` writes it
def orig() -> String:
  "[origins.\"0xaa\"]\n" ++
  "kind = \"git\"\n" ++
  "url = \"https://h/r\"\n" ++
  "rev = \"c0ffee\"\n" ++
  "entry = \"src/lib.bend\"\n" ++
  "root = \".\"\n"

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("an origin says where a vendored package came from",
      L.src.url(L.origin(L.origins(sects(orig())), "0xaa")), "https://h/r")
    Check.eq_str("a package nothing vendored comes from the hub",
      L.src.kind(L.origin(L.origins(sects(orig())), "0xzz")), "hub")

#|ok an origin says where a vendored package came from
#|ok a package nothing vendored comes from the hub

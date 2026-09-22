# lock: where a package comes from, as the ledger records it. The ledger names
# a package or it does not, and that is the only question this file asks.
import Base
import ../lock.bend as L
import ../../manifest/manifest.bend as M
import ../../check/kit.bend as Check

# an ez.toml with one git dependency and one hub dependency
def ledger() -> String:
  "[package]\nname = \"app\"\n" ++
  "\n[deps.wire]\n" ++
  "hash = \"0xaa\"\n" ++
  "git = \"https://h/r\"\n" ++
  "rev = \"c0ffee\"\n" ++
  "root = \".\"\n" ++
  "narHash = \"sha256-zz\"\n" ++
  "entry = \"src/lib.bend\"\n" ++
  "\n[deps.json]\n" ++
  "hash = \"0xbb\"\n"

# the origins that ledger records
def orgs() -> List<&2, L.Origin>:
  L.ledger.read(M.parse(ledger()))

# a word for whether a package is named
def said(named: Bool) -> String:
  Bool.pick(String, named, "named", "unnamed")

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("a git dependency says where it came from",
      L.src.url(L.origin(orgs(), "0xaa")), "https://h/r")
    Check.eq_str("a hub dependency comes from the hub",
      L.src.kind(L.origin(orgs(), "0xbb")), "hub")
    Check.eq_str("a hub dependency is named",
      said(L.known(orgs(), "0xbb")), "named")
    Check.eq_str("a package the ledger does not name is not",
      said(L.known(orgs(), "0xzz")), "unnamed")

#|ok a git dependency says where it came from
#|ok a hub dependency comes from the hub
#|ok a hub dependency is named
#|ok a package the ledger does not name is not

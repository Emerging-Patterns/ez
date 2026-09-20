# ez: the ledger against the import lines, both directions
import Base
import ../drift.bend as D
import ../../manifest/manifest.bend as M
import ../../check/kit.bend as Check

# a ledger naming two packages
def ledger() -> String:
  "[package]\nname = \"app\"\nentry = \"main.bend\"\n" ++
  "\n[deps.sha256]\nhash = \"0xaaaa\"\n" ++
  "\n[deps.wire]\nhash = \"0xbbbb\"\n"

# what the drift report says, on one line
def shown(ls: List<&2, String>) -> String:
  String.join(ls, "; ")

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("an import line names its package",
      D.hash_of("import 0xaaaa/sha256.bend as S"), "0xaaaa")
    Check.eq_str("a local import names none", D.hash_of("import ./run.bend as R"), "")
    Check.eq_str("the same package imported twice counts once",
      shown(D.imported(["import 0xaaaa/a.bend as A", "import 0xaaaa/b.bend as B"])),
      "0xaaaa")
    Check.eq_str("a ledger the source agrees with has no drift",
      shown(D.report(["import 0xaaaa/s.bend as S", "import 0xbbbb/w.bend as W"],
        M.parse(ledger()))), "")
    Check.eq_str("a hash the ledger does not name is drift",
      shown(D.report(["import 0xaaaa/s.bend as S", "import 0xcccc/x.bend as X"],
        M.parse(ledger()))),
      "drift: 0xcccc is imported but ez.toml does not name it; " ++
      "drift: wire = 0xbbbb is in ez.toml but no import line uses it")
    Check.eq_str("a ledger entry nobody imports is drift",
      shown(D.report(["import 0xaaaa/s.bend as S"], M.parse(ledger()))),
      "drift: wire = 0xbbbb is in ez.toml but no import line uses it")

#|ok an import line names its package
#|ok a local import names none
#|ok the same package imported twice counts once
#|ok a ledger the source agrees with has no drift
#|ok a hash the ledger does not name is drift
#|ok a ledger entry nobody imports is drift

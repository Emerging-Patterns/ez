# proofs of laws/ShowOpensWithPackage.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ledger/render.bend as Rend
import ../laws/ShowOpensWithPackage.bend as Laws

def Laws.show_opens_with_package(n, e, b, hb, hbpa, hbpv, ds, ts):
  Eq.starts_nil(Rend.line("name", n) ++ Rend.line("entry", e) ++ Rend.line("bin", b) ++
    Rend.line("hub", hb) ++ Rend.line("publish-as", hbpa) ++ Rend.line("version", hbpv) ++ Rend.deps(ds) ++
    Rend.tools(ts))

# proofs of laws/ShowGoodOpensWithName.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ledger/manifest.bend as M
import ../laws/ShowGoodOpensWithName.bend as Laws

def Laws.show_good_opens_with_name(n, e, _b, _hb, _hbpa, _hbpv, ds, _ts):
  Eq.starts_append(n,
    " " ++ e ++ " " ++ String.join(M.show.deps(ds), " "))

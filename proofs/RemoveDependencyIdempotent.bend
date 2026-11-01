# proofs of laws/RemoveDependencyIdempotent.bend
import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../laws/RemoveDependencyIdempotent.bend as Laws
import ../laws/WithoutIdem.bend as L1
import ./lemmas/PlanEffectFacts.bend as M1

# Removing twice is the inner list dropped twice, which is `without_idem`.
def Laws.remove_idem(m, name):
  match m:
    case M.Manifest{n, e, b, hb, hbpa, hbpv, ds, ts}:
      Equal.cong(List<&2, M.Dep>, M.Manifest,
        xs => M.Manifest{n, e, b, hb, hbpa, hbpv, xs, ts},
        Rend.without(Rend.without(ds, name), name), Rend.without(ds, name),
        L1.without_idem(ds, name))

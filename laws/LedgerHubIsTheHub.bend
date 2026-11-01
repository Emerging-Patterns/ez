import Base
import ../src/ledger/manifest.bend as M

# LAW: a hub the ledger names is the hub, whatever else the ledger holds.
# This is the only place `ez lock` learns a hub from, so two checkouts of one
# commit fetch from the same place whatever their environments say.
law hub_of_names_the_hub:
  for n: String
  for e: String
  for b: String
  for +hb: String
  for +hbpa: String
  for +hbpv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for f: {False{} == String.is_empty(hb) : Bool}
  {M.hub_of(M.Good{M.Manifest{n, e, b, hb, hbpa, hbpv, ds, ts}}) == hb : String}

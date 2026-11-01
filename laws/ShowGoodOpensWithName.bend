import Base
import ../src/ledger/manifest.bend as M

# LAW: and one that did opens with the package's own name
law show_good_opens_with_name:
  for +n: String
  for e: String
  for b: String
  for hb: String
  for hbpa: String
  for hbpv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  {String.starts_with(M.show(M.Good{M.Manifest{n, e, b, hb, hbpa, hbpv, ds, ts}}), n) == True{}
    : Bool}

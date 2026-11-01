import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend

# LAW: the ledger ez assembles opens with the package table, so what it hands
# eztoml to write is a document of tables and not a loose pair.
law show_opens_with_package:
  for n: String
  for e: String
  for b: String
  for hb: String
  for hbpa: String
  for hbpv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  {String.starts_with(Rend.text(M.Manifest{n, e, b, hb, hbpa, hbpv, ds, ts}), "[package]\n") == True{}
    : Bool}

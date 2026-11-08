import Base
import ../src/ledger/manifest.bend as M

# LAW: and so does one whose `[package]` table names no hub
law hub_of_absent_is_bends:
  for n: String
  for e: String
  for b: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Cli>
  {M.hub_of(M.Good{M.Manifest{n, e, b, "", "", "", ds, ts}})
    == "https://hub.bend-lang.com" : String}

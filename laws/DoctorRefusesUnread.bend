import Base
import ../src/ledger/manifest.bend as M
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP

# LAW: and with one that does not parse
law doctor_refuses_unread:
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  for +s: String
  for why: String
  for bad: {M.Bad{why} == M.parse(s) : M.Read}
  {DP.refuses(DW.World{cc, lib, Some{s}, lock, rs}) == True{} : Bool}

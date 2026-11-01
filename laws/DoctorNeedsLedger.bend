import Base
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP

# LAW: with no ez.toml, `ez doctor` fails, after saying what else it found
law doctor_needs_ledger:
  for +cc: String
  for +lib: String
  for +lock: Maybe<&2, String>
  for +rs: List<&2, DW.Reply>
  {DP.refuses(DW.World{cc, lib, None{}, lock, rs}) == True{} : Bool}

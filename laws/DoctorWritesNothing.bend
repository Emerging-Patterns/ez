# `ez doctor` never writes to the project's source files.
import Base
import ../src/lock/plan.bend as P
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP

# LAW: `ez doctor` writes, lays and removes nothing, whatever it found: its
# plan is lines said and how the command ends, so no source file, ledger,
# lock or tree is touched
law doctor_writes_nothing:
  for +w: DW.World
  {P.writes(DP.plan(w)) == False{} : Bool}

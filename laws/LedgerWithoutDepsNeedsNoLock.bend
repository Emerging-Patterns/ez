import Base
import ../src/doctor/plan.bend as DP

# LAW: a ledger with no dependencies never makes the lock a problem, whatever
# the lock names, so `ez doctor` passes a project that has nothing to lock
law lock_needless:
  for hs: List<&2, String>
  {DP.lock.wrong(0n, hs) == False{} : Bool}

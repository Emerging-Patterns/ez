import Base
import ../src/doctor/plan.bend as DP

# LAW: a ledger with dependencies and a lock that names no package is one
law lock_needed:
  for n: Nat
  {DP.lock.wrong(1n+n, []) == True{} : Bool}

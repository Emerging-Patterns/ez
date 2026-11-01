import Base
import ../src/doctor/plan.bend as DP

# LAW: a lock that names a package is never one, however many the ledger has
law lock_names:
  for deps: Nat
  for h: String
  for t: List<&2, String>
  {DP.lock.wrong(deps, h <> t) == False{} : Bool}

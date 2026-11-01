# proofs of laws/DoctorNeedsLedger.bend
import Base
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../laws/DoctorNeedsLedger.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

def Laws.doctor_needs_ledger(cc, lib, lock, rs):
  M1.bad_fails("none here; ez init makes one", cc, lib, lock, rs,
    DP.checked(DW.World{cc, lib, None{}, lock, rs}))

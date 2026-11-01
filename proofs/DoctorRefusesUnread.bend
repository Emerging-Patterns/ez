# proofs of laws/DoctorRefusesUnread.bend
import Base
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../laws/DoctorRefusesUnread.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

def Laws.doctor_refuses_unread(cc, lib, lock, rs, s, why, bad):
  %bad : {DP.refuses.plan(DP.plan.of(DP.ledger.seen(_), cc, lib, lock, rs,
    DP.checked(DW.World{cc, lib, Some{s}, lock, rs}))) == True{} : Bool}
  M1.bad_fails(why, cc, lib, lock, rs, DP.checked(DW.World{cc, lib, Some{s}, lock, rs}))

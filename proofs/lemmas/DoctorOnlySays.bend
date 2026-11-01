# every effect of doctor's plan is a line said
import Base
import ../../src/lock/plan.bend as P
import ../../src/doctor/world.bend as DW
import ../../src/doctor/plan.bend as DP
import ../../laws/DoctorWritesNothing.bend as L1

# ---------------------------------------------------------------------------
# the plan writes nothing

# LAW: the lines of a report, said, write nothing
law says_quiet:
  for ns: List<&2, DP.Note>
  {P.writes.in(DP.says(ns)) == False{} : Bool}

def says_quiet(ns):
  match ns:
    case []:
      {==}
    case h <> t:
      match h:
        case DP.Note{_w, _l}:
          says_quiet(t)

def L1.doctor_writes_nothing(w):
  says_quiet(DP.notes.of(DP.ledger.seen(DW.read(w)), DW.heard(DW.replies(w), DW.Sources{}),
    DW.cc(w), DW.lib(w), DW.lock(w), DW.replies(w), DP.checked(w)))

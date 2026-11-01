# removing a name the ledger does not have is refused
import Base
import ../../src/ledger/render.bend as Rend
import ../../src/remove/plan.bend as RP
import ../../laws/RemoveRefusesAbsent.bend as L1

# The read is rewritten to the ledger, and the scan for the name to the False
# the premise gives, which is the arm that refuses.
def L1.remove_refuses_absent(name, _s, ignore, m, good, no):
  %good : {RP.refuses.plan(RP.plan.read(_, name, ignore)) == True{} : Bool}
  %no : {RP.refuses.plan(RP.plan.has(Bool.and(_, Rend.renderable(Rend.remove(m, name))),
    m, name, ignore)) == True{} : Bool}
  {==}

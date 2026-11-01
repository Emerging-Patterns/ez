# proofs of laws/HubTargetRunsHubPlanner.bend
import Base
import ../src/lock/plan.bend as P
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H
import ../laws/HubTargetRunsHubPlanner.bend as Laws

def Laws.add_runs_hub(w, n):
  %Equal.sym(Bool, A.named(w), True{}, n) : {AP.command.of(_, w) == H.plan(w) : P.Plan}
  {==}

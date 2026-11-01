# proofs of laws/OtherTargetRunsGitPlanner.bend
import Base
import ../src/lock/plan.bend as P
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../laws/OtherTargetRunsGitPlanner.bend as Laws

# The command's planner is picked by whether the target is a name.
def Laws.add_runs_plan(w, g):
  %Equal.sym(Bool, A.named(w), False{}, g) : {AP.command.of(_, w) == AP.plan(w) : P.Plan}
  {==}

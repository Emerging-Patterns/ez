# What a command's interpreter is told to do next agrees with its planner.
# When the step for a World runs a plan, that plan is exactly the command's
# plan of the same World, so the plan the laws are stated over is the one that
# runs. For `ez fetch` and `ez doctor`, when the step asks, it asks exactly
# the questions the World still leaves open (`wants`), and it runs only once
# there are none. The workspace doctor runs its own plan and asks exactly
# what the doctor asks. Holds for `ez fetch`, `ez doctor` (alone and in a
# workspace), `ez publish` and `ez tool run`, `install` and `upgrade`.
#
# Internal, not interface: this ties each `step` to the `plan` and `wants`
# the command's other laws are stated over.
import Base
import ../src/lock/plan.bend as P
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/ws/doctor.bend as WD
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP
import ../src/tool/world.bend as TW
import ../src/tool/plan.bend as TP

# the plan a fetch step runs, or `other` when it asks instead
def ran.fetch(st: FP.Step, other: P.Plan) -> P.Plan:
  match st:
    case FP.Asking{_asks}:
      other
    case FP.Run{pl}:
      pl

# the questions a fetch step asks, none when it runs a plan
def asked.fetch(st: FP.Step) -> List<&2, F.Ask>:
  match st:
    case FP.Asking{asks}:
      asks
    case FP.Run{_pl}:
      []

# the plan a doctor step runs, or `other` when it asks instead
def ran.doctor(st: DP.Step, other: P.Plan) -> P.Plan:
  match st:
    case DP.Asking{_asks}:
      other
    case DP.Run{pl}:
      pl

# the questions a doctor step asks, none when it runs a plan
def asked.doctor(st: DP.Step) -> List<&2, DW.Ask>:
  match st:
    case DP.Asking{asks}:
      asks
    case DP.Run{_pl}:
      []

# the plan a publish step runs, or `other` when it asks instead
def ran.publish(st: PP.Step, other: P.Plan) -> P.Plan:
  match st:
    case PP.Asking{_asks}:
      other
    case PP.Run{pl}:
      pl

# the plan a tool step runs, or `other` when it asks instead
def ran.tool(st: TP.Step, other: TP.Plan) -> TP.Plan:
  match st:
    case TP.Asking{_asks, _ups}:
      other
    case TP.Run{pl}:
      pl

# LAW: a fetch step that runs a plan runs the fetch's plan of that World
law fetch_step_runs_plan:
  for +world: F.World
  {ran.fetch(FP.step(world), FP.plan(world)) == FP.plan(world) : P.Plan}

# LAW: and one that asks asks exactly what the World leaves open
law fetch_step_asks_wants:
  for +world: F.World
  {asked.fetch(FP.step(world)) == FP.wants(world) : List<&2, F.Ask>}

# LAW: a doctor step that runs a plan runs the doctor's plan of that World
law doctor_step_runs_plan:
  for +world: DW.World
  {ran.doctor(DP.step(world), DP.plan(world)) == DP.plan(world) : P.Plan}

# LAW: and one that asks asks exactly what the World leaves open
law doctor_step_asks_wants:
  for +world: DW.World
  {asked.doctor(DP.step(world)) == DP.wants(world) : List<&2, DW.Ask>}

# LAW: the workspace doctor runs its own plan of the World
law workspace_doctor_step_runs_plan:
  for back: WD.Back
  for +world: DW.World
  {ran.doctor(WD.step(back, world), WD.plan(back, world)) == WD.plan(back, world) : P.Plan}

# LAW: and asks exactly what the doctor asks
law workspace_doctor_step_asks:
  for back: WD.Back
  for +world: DW.World
  {asked.doctor(WD.step(back, world)) == asked.doctor(DP.step(world)) : List<&2, DW.Ask>}

# LAW: a publish step that runs a plan runs the publish's plan of that World
law publish_step_runs_plan:
  for +world: PW.World
  {ran.publish(PP.step(world), PP.plan(world)) == PP.plan(world) : P.Plan}

# LAW: a tool step that runs a plan runs the tool command's plan of that World
law tool_step_runs_plan:
  for +world: TW.World
  {ran.tool(TP.step(world), TP.plan(world)) == TP.plan(world) : TP.Plan}

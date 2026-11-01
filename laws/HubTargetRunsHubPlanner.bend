import Base
import ../src/lock/plan.bend as P
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/hub.bend as H

# LAW: and one that is runs the hub planner
law add_runs_hub:
  for +w: A.World
  for n: {A.named(w) == True{} : Bool}
  {AP.command(w) == H.plan(w) : P.Plan}

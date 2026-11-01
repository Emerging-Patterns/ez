import Base
import ../src/lock/plan.bend as P
import ../src/relock/relock.bend as R
import ../src/remove/relock.bend as RR
import ../src/ws/relock.bend as Rel

# LAW: `ez remove` in a workspace that refuses writes, lays and removes
# nothing
law remove_ws_refusal_writes_nothing:
  for +root: Rel.Rooted
  for +w: RR.World
  for r: {R.refuses(Rel.remove.plan(root, w)) == True{} : Bool}
  {P.writes(Rel.remove.plan(root, w)) == False{} : Bool}

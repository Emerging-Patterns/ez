import Base
import ../src/lock/plan.bend as P
import ../src/add/relock.bend as AR
import ../src/relock/relock.bend as R
import ../src/ws/relock.bend as Rel

# LAW: `ez add` in a workspace that refuses writes, lays and removes nothing
law add_ws_refusal_writes_nothing:
  for +root: Rel.Rooted
  for +w: AR.World
  for r: {R.refuses(Rel.add.plan(root, w)) == True{} : Bool}
  {P.writes(Rel.add.plan(root, w)) == False{} : Bool}

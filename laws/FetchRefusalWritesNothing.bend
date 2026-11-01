import Base
import ../src/lock/plan.bend as P
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP

# LAW: `ez fetch` that refuses writes, lays and removes nothing: no tree
# under BEND_LIB, not even one of a package that checked before the one that
# failed, and a tree already there is not removed. Its plan has no effect at
# all; the reason is how it ends.
law fetch_refusal_writes_nothing:
  for +w: F.World
  for r: {FP.refuses(w) == True{} : Bool}
  {P.writes(FP.plan(w)) == False{} : Bool}

import Base
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/ws/up.bend as UUp

# LAW: an upgrade at a workspace root that refuses writes nothing: no
# ledger, no lock, no tree, and no source it would have rewritten
# (laws/RefusalWritesNothing.bend). The World it refuses on is the one it
# plans on, with every moved member's import lines rewritten
# (laws/HashedMemberMovesCascade.bend).
law up_refusal_writes_nothing:
  for +back: UUp.Back
  for +world: W.World
  for +er: {P.refuses(UUp.plans.on(back, world)) == True{} : Bool}
  {P.writes(UUp.plan(back, world)) == False{} : Bool}

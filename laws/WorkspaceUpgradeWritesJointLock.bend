import Base
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/ws/up.bend as UUp

# LAW: and the lock it writes is the one the lock planner plans on the joint
# ledger: writing the ledgers back in place of the joint one, and the sources
# the member moves rewrite ahead of the plan, leaves the lock as it was
law up_writes_the_lock:
  for +back: UUp.Back
  for +world: W.World
  for es: {UUp.stale(back, world) == "" : String}
  {P.put.plan(UUp.plan(back, world), P.lockfile()) == P.put(UUp.plans.on(back, world), P.lockfile()) : P.Wrote}

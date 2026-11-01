import Base
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W

# LAW: a plain lock writes no path but the lock's: whatever else is at a path,
# a ledger among it, it leaves as it was. In a workspace the lock is planned
# from the joint ledger (src/ws/joint.bend) on a World like any other, so this
# holds of the workspace's lock too.
law plain_lock_writes_only_lock:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  for +path: String
  for ep: {String.eq(P.lockfile(), path) == False{} : Bool}
  {P.put(w, path) == P.Kept{} : P.Wrote}

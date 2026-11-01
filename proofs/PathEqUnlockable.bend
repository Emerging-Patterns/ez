# proofs of laws/PathEqUnlockable.bend
import Base
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../src/add/world.bend as A
import ../laws/PathEqUnlockable.bend as Laws

# What the lock may hold. A path holding `=` makes its package's `paths.ok`
# False, and an `and` with a False half is False whichever side it is on.

# LAW: an `and` whose right half is False is False
law and_false_lock:
  for a: Bool
  {Bool.and(a, False{}) == False{} : Bool}

def and_false_lock(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.path_eq_unlockable(hash, src, at, sum, fs, rest, ts, hub, e):
  %e : {Bool.and(P.clean(hub), Bool.and(Bool.and(Bool.and(Bool.and(_,
    P.paths.ok(fs)), Bool.and(P.clean.all(P.pack.values(L.Pack{hash, src,
    K.Item{at, sum} <> fs})), Bool.not(L.has(rest, hash)))), P.packs.ok(rest)),
    P.tools.ok(ts))) == False{} : Bool}
  and_false_lock(P.clean(hub))

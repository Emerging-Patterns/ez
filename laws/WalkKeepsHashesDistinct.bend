import Base
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ./defs/DistinctPackHashes.bend as D1

# LAW: the walk resolves each hash at most once, one step at a time: a step
# passes over a hash it has already resolved
law walk_keeps_hashes_distinct:
  for +fuel: Nat
  for +orgs: List<&2, L.Origin>
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  for +wk: P.Walk
  for +e: {D1.packs.distinct(P.walk.packs(wk)) == True{} : Bool}
  {D1.packs.distinct(P.walk.packs(P.walk(fuel, orgs, ns, js, wk))) == True{} : Bool}

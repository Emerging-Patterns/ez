import Base
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ./defs/LockInputs.bend as D1

# LAW: every package the walk resolves carries the source the ledger records
# for its hash, one step at a time
law walk_pins_ledger_sources:
  for +fuel: Nat
  for +orgs: List<&2, L.Origin>
  for +ns: List<&2, L.Name>
  for +js: List<&2, W.Judged>
  for +wk: P.Walk
  for +e: {D1.pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  {D1.pinned.all(orgs, P.walk.packs(P.walk(fuel, orgs, ns, js, wk)))
    == P.walk.packs(P.walk(fuel, orgs, ns, js, wk)) : List<&2, L.Pack>}

import Base
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ./defs/NamesLaid.bend as D1

# LAW: a lock that is made lays a names file for every name the lock it
# writes records, with the hash it records, and none other
law lock_lays_its_names:
  for +w: W.World
  for +t: String
  for d: {P.Doc{t} == P.decide(W.inputs(w)) : P.Doc}
  {D1.names.laid(P.effects(P.plan(w))) == L.names.read(t) : List<&2, L.Name>}

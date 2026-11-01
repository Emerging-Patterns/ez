# `ez lock` and `ez fetch` lay `BEND_LIB/names/<name>@<version>` holding the
# hash the lock records, for every name it records, and `ez add
# <name>@<version>` lays the file of the name it adds. `ez fetch` rewrites a
# file that names another hash, and says so. `ez doctor` fails when a file is
# missing or names another hash.
#
# also rests on: laws/LockLaysItsNames.bend
import Base
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/doctor/world.bend as DW
import ../src/doctor/plan.bend as DP
import ../src/add/world.bend as A
import ../src/add/hub.bend as H
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP
import ./defs/NamesLaid.bend as D1
import ./defs/NamesLaidByParts.bend as D2

# LAW: a name the lock records whose file under BEND_LIB is missing, or names
# another hash than the lock does, fails `ez doctor`: bend reads that file
# before it would ask the hub, so a wrong one builds another package
law doctor_wrong_name_fails:
  for +w: DW.World
  for x: String
  for xs: List<&2, String>
  for b: {x <> xs == DP.names.wrong(DP.lock.names(DW.lock(w)), DW.replies(w)) : List<&2, String>}
  {DP.refuses(w) == True{} : Bool}

# LAW: an add that does not refuse lays the name's file,
# `$BEND_LIB/names/<name>@<version>`, holding the hash it records, and no
# other, so bend reads the name without asking the hub
law add_named_lays_name:
  for +w: A.World
  for +ok: {H.refuses(w) == False{} : Bool}
  {H.names.laid(P.effects(H.plan(w))) == [L.Name{A.target(w), M.dep.hash(H.added(w))}]
    : List<&2, L.Name>}

# LAW: a name whose file BEND_LIB lacks is laid, with the lock's hash
law fetch_lays_missing_name:
  for +rs: List<&2, F.Reply>
  for +nv: String
  for +hash: String
  for v: {True{} == L.name.valid(L.Name{nv, hash}) : Bool}
  for g: {F.Heard{F.Held{None{}}} == F.heard(rs, F.Named{nv}) : F.Heard}
  {FP.name.part(rs, L.Name{nv, hash}) == FP.NmPut{nv, hash, ""} : FP.Nm}

# LAW: and one whose file names another hash is laid over it, saying what it
# named, since the lock wins over it
law fetch_rewrites_name:
  for +rs: List<&2, F.Reply>
  for +nv: String
  for +hash: String
  for +x: String
  for v: {True{} == L.name.valid(L.Name{nv, hash}) : Bool}
  for g: {F.Heard{F.Held{Some{x}}} == F.heard(rs, F.Named{nv}) : F.Heard}
  for ne: {False{} == String.eq(String.trim(x), hash) : Bool}
  {FP.name.part(rs, L.Name{nv, hash}) == FP.NmPut{nv, hash, String.trim(x)} : FP.Nm}

# LAW: a name bend would not read back refuses the fetch, rather than laying
# a file at a path the lock chose that bend would not read
law fetch_refuses_unread_name:
  for +rs: List<&2, F.Reply>
  for +nv: String
  for +hash: String
  for v: {False{} == L.name.valid(L.Name{nv, hash}) : Bool}
  {FP.names.outcome([FP.name.part(rs, L.Name{nv, hash})])
    == P.Refused{"ez: the lock names " ++ nv ++ " as " ++ hash ++
      ", which bend would not read back; run ez lock"} : P.Outcome}

# LAW: a fetch that succeeds lays the names file of every name its parts lay,
# and no other
law fetch_lays_the_names:
  for +w: F.World
  for ok: {FP.refuses(w) == False{} : Bool}
  {D1.names.laid(FP.effects(FP.plan(w))) == D2.puts(FP.name.parts.of(F.sects(w), w)) : List<&2, L.Name>}

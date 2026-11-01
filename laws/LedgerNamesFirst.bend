import Base
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W

# LAW: a name ez.toml records resolves to the hash ez.toml records beside
# it, whatever the answers say
law ledger_names_first:
  for +led: M.Read
  for +js: List<&2, W.Judged>
  for +nv: String
  for f: {False{} == String.is_empty(L.name.find(L.ledger.names(led), nv)) : Bool}
  {L.name.find(P.table(led, js), nv) == L.name.find(L.ledger.names(led), nv) : String}

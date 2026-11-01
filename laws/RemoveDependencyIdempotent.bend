# Removing a dependency from a ledger model twice is removing it once.
import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/lock/plan.bend as P
import ../src/remove/plan.bend as RP

# LAW: removing a dependency twice is removing it once, which is what makes
# `ez remove` safe to run on a ledger it already edited.
law remove_idem:
  for m: M.Manifest
  for +name: String
  {Rend.remove(Rend.remove(m, name), name) == Rend.remove(m, name) : M.Manifest}

# LAW: `ez remove` that does not refuse writes to ez.toml exactly the ledger
# `Rend.remove` gives, the edit `remove_idem` says is the same done twice
law remove_edits_ledger:
  for +name: String
  for +s: String
  for +ignore: String
  for +m: M.Manifest
  for +good: {M.Good{m} == M.parse(s) : M.Read}
  for ok: {RP.refuses(RP.World{name, Some{s}, ignore}) == False{} : Bool}
  {P.put.plan(RP.plan(RP.World{name, Some{s}, ignore}), "ez.toml")
    == P.Put{Rend.show(Rend.remove(m, name))} : P.Wrote}

import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend

# LAW: dropping a dependency drops every entry of that name, so dropping twice
# is dropping once. `ez remove` on a ledger it already edited is a no-op.
law without_idem:
  for ds: List<&2, M.Dep>
  for +name: String
  {Rend.without(Rend.without(ds, name), name) == Rend.without(ds, name) : List<&2, M.Dep>}

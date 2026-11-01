import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend

# LAW: rendering a list of dependencies renders each of them, in order, and
# adds nothing between. Splitting the list splits the text at the same place,
# which is what makes the file the ledger and not a summary of it.
law deps_splits:
  for as: List<&2, M.Dep>
  for +bs: List<&2, M.Dep>
  {Rend.deps(List.append(&2, M.Dep, as, bs)) == Rend.deps(as) ++ Rend.deps(bs) : String}

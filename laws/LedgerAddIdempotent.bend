import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend

# LAW: adding a dependency twice is adding it once, which is what makes
# `ez add` safe to run on a ledger that already names the package.
law add_idem:
  for m: M.Manifest
  for +d: M.Dep
  {Rend.add(Rend.add(m, d), d) == Rend.add(m, d) : M.Manifest}

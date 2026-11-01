import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend

# LAW: a dependency's section is headed by that dependency's own name
law dep_opens_its_section:
  for +n: String
  for h: String
  for e: String
  for s: M.Source
  {String.starts_with(Rend.dep(M.Dep{n, h, e, s}), "\n[deps." ++ n) == True{}
    : Bool}

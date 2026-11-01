import Base
import ../src/ledger/manifest.bend as M

# LAW: a lookup answers with the first dependency of that name, whole
law find_first:
  for +n: String
  for h: String
  for en: String
  for s: M.Source
  for t: List<&2, M.Dep>
  {M.find(M.Dep{n, h, en, s} <> t, n) == M.Dep{n, h, en, s} : M.Dep}

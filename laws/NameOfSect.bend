import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: a section answers with the name it was written with
law name_of_sect:
  for +n: String
  for ps: List<&2, T.Kv>
  {M.name_of(T.Sect{n, ps}) == n : String}

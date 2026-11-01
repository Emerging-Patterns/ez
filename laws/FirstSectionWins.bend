import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/add/world.bend as A

# LAW: a document answers a section name with the pairs of the first section
# of that name. A later table of the same name never shadows an earlier one,
# which matters because a ledger a person edited may well hold two.
law pairs_of_first:
  for +name: String
  for ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  {M.pairs_of(T.Sect{name, ps} <> ss, name) == ps : List<&2, T.Kv>}

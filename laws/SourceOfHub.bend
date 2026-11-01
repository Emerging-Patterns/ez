import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: a dependency section that names no repo is a hub package. This is the
# one place ez decides that a package needs no checkout, so it must turn on
# the `git` key being absent and on nothing else.
law source_of_hub:
  for +pairs: List<&2, T.Kv>
  for e: {True{} == String.is_empty(M.value(pairs, "git")) : Bool}
  {M.source_of(pairs) == M.Hub{""} : M.Source}

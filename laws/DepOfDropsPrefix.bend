import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: a `[deps.<name>]` section is a dependency of that name, with the
# prefix off and nothing else taken with it.
law dep_of_drops_prefix:
  for +name: String
  for +pairs: List<&2, T.Kv>
  {M.dep.name(M.dep_of("deps." ++ name, pairs)) == name : String}

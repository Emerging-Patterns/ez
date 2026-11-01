import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: every `[deps.<name>]` section becomes a dependency, in the order the
# document wrote them.
law deps_takes_dep_sections:
  for +name: String
  for +ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  {M.deps(T.Sect{"deps." ++ name, ps} <> ss)
    == M.dep_of("deps." ++ name, ps) <> M.deps(ss) : List<&2, M.Dep>}

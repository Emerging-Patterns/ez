import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: and a section that is not one is passed over rather than read as one
law deps_skips_other_sections:
  for +n: String
  for ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  for e: {False{} == String.starts_with(n, "deps.") : Bool}
  {M.deps(T.Sect{n, ps} <> ss) == M.deps(ss) : List<&2, M.Dep>}

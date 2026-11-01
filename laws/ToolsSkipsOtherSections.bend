import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: and a section that is not one is passed over
law tools_skips_other_sections:
  for +n: String
  for ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  for e: {False{} == String.starts_with(n, "tools.") : Bool}
  {M.tools(T.Sect{n, ps} <> ss) == M.tools(ss) : List<&2, M.Tool>}

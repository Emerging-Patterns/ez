import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/add/world.bend as A

# LAW: every `[tools.<name>]` section becomes a pinned CLI, in the order the
# document wrote them. A dependency section is not one of them.
law tools_takes_tool_sections:
  for +name: String
  for +ps: List<&2, T.Kv>
  for ss: List<&2, T.Sect>
  {M.tools(T.Sect{"tools." ++ name, ps} <> ss)
    == M.tool_of("tools." ++ name, ps) <> M.tools(ss) : List<&2, M.Cli>}

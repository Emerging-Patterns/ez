import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M

# LAW: a `[tools.<name>]` section is a pinned CLI of that name, with the
# prefix off and nothing else taken with it.
law tool_of_drops_prefix:
  for +name: String
  for +pairs: List<&2, T.Kv>
  {M.tool.name(M.tool_of("tools." ++ name, pairs)) == name : String}

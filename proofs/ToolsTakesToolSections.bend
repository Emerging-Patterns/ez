# proofs of laws/ToolsTakesToolSections.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../laws/ToolsTakesToolSections.bend as Laws

def Laws.tools_takes_tool_sections(name, ps, ss):
  Equal.cong(Bool, List<&2, M.Tool>,
    b => M.tools.put(b, T.Sect{String.append("tools.", name), ps}, M.tools(ss)),
    String.starts_with(String.append("tools.", name), "tools."), True{},
    Eq.starts_append("tools.", name))

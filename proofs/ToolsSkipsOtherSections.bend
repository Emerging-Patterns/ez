# proofs of laws/ToolsSkipsOtherSections.bend
import Base
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../laws/ToolsSkipsOtherSections.bend as Laws

def Laws.tools_skips_other_sections(n, ps, ss, e):
  %e : {M.tools.put(_, T.Sect{n, ps}, M.tools(ss)) == M.tools(ss)
    : List<&2, M.Cli>}
  {==}

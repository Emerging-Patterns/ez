# proofs of laws/ToolOpensItsSection.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ledger/render.bend as Rend
import ../laws/ToolOpensItsSection.bend as Laws

def Laws.tool_opens_its_section(n, e, b, s):
  Eq.starts_append(n, "]\n" ++ Rend.source(s) ++ Rend.line("entry", e) ++ Rend.line("bin", b))

import Base
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend

# LAW: a tool's section is headed by that tool's own name
law tool_opens_its_section:
  for +n: String
  for e: String
  for b: String
  for s: M.Source
  {String.starts_with(Rend.tool(M.Tool{n, e, b, s}), "\n[tools." ++ n) == True{}
    : Bool}

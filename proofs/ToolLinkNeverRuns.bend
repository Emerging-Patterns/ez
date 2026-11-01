# proofs of laws/ToolLinkNeverRuns.bend
import Base
import ../src/tool/plan.bend as TP
import ../laws/ToolLinkNeverRuns.bend as Laws
import ./lemmas/LinkNeverStarts.bend as M1

def Laws.tool_link_never_runs(w, a, act, l):
  M1.never(TP.decide(w), w, a, act, l)

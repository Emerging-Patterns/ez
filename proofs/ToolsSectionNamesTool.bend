# proofs of laws/ToolsSectionNamesTool.bend
import Base
import ../laws/ToolsSectionNamesTool.bend as Laws
import ./lemmas/StringDropZero.bend as M1

def Laws.tool_of_drops_prefix(name, _pairs):
  M1.drop_zero_ledger(name)

# proofs of laws/HubImportNeeds0x.bend
import Base
import ../laws/HubImportNeeds0x.bend as Laws

def Laws.hub_needs_0x(s, e):
  %e : {Bool.and(_, String.contains(s, "/")) == False{} : Bool}
  {==}

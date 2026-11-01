# proofs of laws/HubNeeds0x.bend
import Base
import ../laws/HubNeeds0x.bend as Laws

def Laws.hub_needs_0x(s, e):
  %e : {Bool.and(_, String.contains(s, "/")) == False{} : Bool}
  {==}

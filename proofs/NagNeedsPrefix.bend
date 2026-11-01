# proofs of laws/NagNeedsPrefix.bend
import Base
import ../laws/NagNeedsPrefix.bend as Laws

def Laws.nag_needs_prefix(s, e):
  %e : {Bool.and(_, String.ends_with(s, " is available: run bend update"))
    == False{} : Bool}
  {==}

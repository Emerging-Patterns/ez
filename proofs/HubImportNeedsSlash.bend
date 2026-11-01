# proofs of laws/HubImportNeedsSlash.bend
import Base
import ../laws/HubImportNeedsSlash.bend as Laws

# LAW: `and` with False on the right is False
law and_false_pkg:
  for b: Bool
  {Bool.and(b, False{}) == False{} : Bool}

def and_false_pkg(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.hub_needs_slash(s, e):
  %e : {Bool.and(String.starts_with(s, "0x"), _) == False{} : Bool}
  and_false_pkg(String.starts_with(s, "0x"))

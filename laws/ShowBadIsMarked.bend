import Base
import ../src/ledger/manifest.bend as M

# LAW: a ledger that did not read says so before it says anything else
law show_bad_is_marked:
  for why: String
  {String.starts_with(M.show(M.Bad{why}), "error: ") == True{} : Bool}

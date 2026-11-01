# proofs of laws/FetchNeedsLock.bend
import Base
import ../laws/FetchNeedsLock.bend as Laws

# No lock refuses whether or not there is a ledger.
def Laws.fetch_needs_lock(_here, led, _rs):
  match led:
    case False{}:
      {==}
    case True{}:
      {==}

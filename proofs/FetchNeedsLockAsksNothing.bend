# proofs of laws/FetchNeedsLockAsksNothing.bend
import Base
import ../laws/FetchNeedsLockAsksNothing.bend as Laws

def Laws.fetch_needs_lock_asks_nothing(_here, led, _rs):
  match led:
    case False{}:
      {==}
    case True{}:
      {==}

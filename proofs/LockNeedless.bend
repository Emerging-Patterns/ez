# proofs of laws/LockNeedless.bend
import Base
import ../laws/LockNeedless.bend as Laws

# ---------------------------------------------------------------------------
# the lock's verdict turns on the list first, so the no-dependency law splits
# on it and the other two are the arm they name

def Laws.lock_needless(hs):
  match hs:
    case []:
      {==}
    case _h <> _t:
      {==}

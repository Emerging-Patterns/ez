# proofs of laws/PlainLockLeavesLedger.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/lock/world.bend as W
import ../laws/PlainLockLeavesLedger.bend as Laws

def Laws.plain_lock_ledger_next(w, e):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, only, here}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {P.ledger.next(W.World{W.Args{True{}, only, here}, ledger,
                listing, replies, ups}) == W.parsed(ledger) : M.Read}, e)
            case False{}:
              {==}

# proofs of laws/PlainLockAsksNoUpgrade.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/lock/up.bend as Up
import ../src/add/world.bend as A
import ../laws/PlainLockAsksNoUpgrade.bend as Laws

# A plain World's args say no `--upgrade`; the other arm contradicts the
# premise, and in this one the upgrade is `Up.plain`, which asks nothing.
def Laws.plain_lock_asks_no_upgrade(w, e):
  match w:
    case W.World{args, +ledger, listing, replies, ups}:
      match args:
        case W.Args{up, only, here}:
          match up:
            case True{}:
              Eq.bit.absurd2(&2, {P.wants.up(W.World{W.Args{True{}, only, here}, ledger,
                listing, replies, ups}) == [] : List<&2, Up.Ask>}, e)
            case False{}:
              {==}

import Base
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W

# LAW: and the ledger a plain lock leaves is ez.toml as it is
law plain_lock_ledger_next:
  for w: W.World
  for e: {W.args.upgrade(w) == False{} : Bool}
  {P.ledger.next(w) == W.parsed(W.ledger.of(w)) : M.Read}

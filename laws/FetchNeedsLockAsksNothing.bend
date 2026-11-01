import Base
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP

# LAW: and asks nothing first
law fetch_needs_lock_asks_nothing:
  for +here: String
  for led: Bool
  for rs: List<&2, F.Reply>
  {FP.wants(F.World{here, led, None{}, rs}) == [] : List<&2, F.Ask>}

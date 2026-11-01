import Base
import ../src/fetch/world.bend as F
import ../src/fetch/plan.bend as FP

# LAW: with no ez.lock.toml, `ez fetch` refuses too, as `uv sync --frozen`
# does, rather than resolving one: a fetch writes no lock
law fetch_needs_lock:
  for +here: String
  for led: Bool
  for rs: List<&2, F.Reply>
  {FP.refuses(F.World{here, led, None{}, rs}) == True{} : Bool}

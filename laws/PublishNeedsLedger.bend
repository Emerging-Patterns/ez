import Base
import ../src/pub/world.bend as PW
import ../src/pub/plan.bend as PP

# LAW: with no ez.toml, `ez publish` refuses outright, sending nothing,
# rather than guessing an entry
law pub_needs_ledger:
  for +here: String
  for rs: List<&2, PW.Reply>
  {PP.stops(PW.World{here, None{}, rs}) == True{} : Bool}

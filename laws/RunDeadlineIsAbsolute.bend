import Base
import ../src/ez/clock.bend as Clock

# clock: the deadline the run effect holds. `date` and `test` are not
# among them.

# LAW: the deadline the run effect keeps is the absolute second
law by_effect_keeps:
  for +d: String
  for e: {False{} == String.is_empty(d) : Bool}
  {Clock.by.effect(d) == d : String}

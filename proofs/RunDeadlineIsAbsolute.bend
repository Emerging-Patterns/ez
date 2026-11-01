# proofs of laws/RunDeadlineIsAbsolute.bend
import Base
import ../laws/RunDeadlineIsAbsolute.bend as Laws

# The clock's pure half: a non-empty deadline is rewritten into the
# pick that keeps it.

def Laws.by_effect_keeps(d, e):
  %e : {Bool.pick(String, _, "0", d) == d : String}
  {==}

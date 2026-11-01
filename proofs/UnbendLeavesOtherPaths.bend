# proofs of laws/UnbendLeavesOtherPaths.bend
import Base
import ../laws/UnbendLeavesOtherPaths.bend as Laws

# The strip asks one question, and the hypothesis answers it.
def Laws.unbend_plain(p, e):
  %e : {Bool.pick(String, _, String.take(p, Nat.sub(String.length(p), 5n)), p)
    == p : String}
  {==}

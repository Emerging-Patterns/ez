# proofs of laws/TailPlain.bend
import Base
import ../laws/SplitPlain.bend as L1
import ../laws/TailPlain.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

# One component reversed, taken and reversed again is still that component,
# and joining a single component with any separator writes no separator.
def Laws.tail_plain(p, q, e):
  Equal.cong(List<&2, String>, String,
    ps => String.join(List.reverse(&2, String,
      List.take(&2, String, List.reverse(&2, String, ps), 1n+q)), "/"),
    String.split(p, '/'), [p], L1.split_plain(p, e))

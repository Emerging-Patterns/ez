# proofs of laws/ClimbCancelsComponent.bend
import Base
import ../src/pkg/path.bend as Path
import ../src/add/world.bend as A
import ../laws/ClimbCancelsComponent.bend as Laws

# A climb against a kept component asks one question, and the hypothesis
# answers it.
def Laws.up_cancels(_abs, h, t, e):
  %e : {Path.up.back(_, h, t) == t : List<&2, String>}
  {==}

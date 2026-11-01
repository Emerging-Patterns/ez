# proofs of laws/SlashlessPathIsItsOwnBase.bend
import Base
import ../src/pkg/path.bend as Path
import ../laws/SlashlessPathIsItsOwnBase.bend as Laws
import ../laws/SlashlessPathSplitsToItself.bend as L1
import ./lemmas/PlanEffectFacts.bend as M1

# One component is the last component.
def Laws.base_plain(p, e):
  Equal.cong(List<&2, String>, String, ps => Path.base.last(ps),
    String.split(p, '/'), [p], L1.split_plain(p, e))

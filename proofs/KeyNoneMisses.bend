# proofs of laws/KeyNoneMisses.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/ez/key.bend as KKey
import ../laws/KeyNoneMisses.bend as Laws

# the resolved commit has a first char, so the empty one on record is not
# equal to it. The empty resolved commit is the arm the premise rules out.
def Laws.key_none_misses(r, f, b, e):
  match r:
    case SNil{}:
      Eq.bit.absurd(&2, {KKey.reuse(KKey.none(), KKey.Stamp{"", f, b}) == False{} : Bool},
        e)
    case SCon{_h, _t}:
      {==}

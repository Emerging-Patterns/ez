# proofs of laws/RecordedPackageIsNamed.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/lock.bend as L
import ../laws/RecordedPackageIsNamed.bend as Laws

# The head's hash compared with itself is the arm that answers at once.
def Laws.known_first(h, _s, rest):
  Equal.cong(Bool, Bool, b => L.any.step(b, _u => L.known(rest, h)),
    String.eq(h, h), True{}, Eq.string_eq_self(h))

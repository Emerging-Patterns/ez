# proofs of laws/FirstOriginWins.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/lock.bend as L
import ../laws/FirstOriginWins.bend as Laws

def Laws.origin_first(h, s, rest):
  Equal.cong(Bool, L.Src, b => Bool.pick(L.Src, b, s, L.origin(rest, h)),
    String.eq(h, h), True{}, Eq.string_eq_self(h))

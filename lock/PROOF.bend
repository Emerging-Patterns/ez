# lock: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./lock.bend as L
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

def Laws.origin_first(h, s, rest):
  Equal.cong(Bool, L.Src, b => Bool.pick(L.Src, b, s, L.origin(rest, h)),
    String.eq(h, h), True{}, Eq.string_eq_self(h))

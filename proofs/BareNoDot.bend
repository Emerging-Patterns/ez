# proofs of laws/BareNoDot.bend
import Base
import ../laws/BareNoDot.bend as Laws
import ./lemmas/BareKeyDots.bend as M1

def Laws.bare_no_dot(a, b):
  M1.bare_dot(a, b)

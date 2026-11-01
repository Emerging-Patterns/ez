# proofs of laws/NonTrailerLineSkipped.bend
import Base
import ../src/ez/gate.bend as G
import ../laws/NonTrailerLineSkipped.bend as Laws

def Laws.want_skips(h, t, e):
  %e : {G.want.put(_, h, G.want(t)) == G.want(t) : List<&2, String>}
  {==}

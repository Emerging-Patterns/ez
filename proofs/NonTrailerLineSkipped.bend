# proofs of laws/NonTrailerLineSkipped.bend
import Base
import ../src/ez/gate.bend as G
import ../laws/NonTrailerLineSkipped.bend as Laws

def Laws.want_skips(h, t, e):
  %e : {G.want.put(_, h, G.want(t)) == G.want(t) : List<&2, String>}
  {==}

def Laws.trailer_skips(_text, h, t, e, ne):
  %e : {String.join(G.want(_), "\n") == String.join(G.want(t), "\n") : String}
  %Equal.sym(List<&2, String>, G.want(h <> t), G.want(t), Laws.want_skips(h, t, ne))
    : {String.join(_, "\n") == String.join(G.want(t), "\n") : String}
  {==}

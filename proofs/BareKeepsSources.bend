# proofs of laws/BareKeepsSources.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/BareKeepsSources.bend as Laws

def Laws.bare_keeps_sources(h, t, src):
  %src : {K.bare.pick(_, h, K.bare(t)) == h <> K.bare(t) : List<&2, K.Item>}
  {==}

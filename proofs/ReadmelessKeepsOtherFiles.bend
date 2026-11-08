# proofs of laws/ReadmelessKeepsOtherFiles.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/ReadmelessKeepsOtherFiles.bend as Laws

def Laws.readmeless_keeps_others(h, t, other):
  %other : {K.readmeless.pick(_, h, K.readmeless(t)) == h <> K.readmeless(t) : List<&2, K.Item>}
  {==}

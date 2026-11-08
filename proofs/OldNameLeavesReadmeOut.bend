# proofs of laws/OldNameLeavesReadmeOut.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/OldNameLeavesReadmeOut.bend as Laws

def Laws.readmeless_drops_readme(h, t, readme):
  %readme : {K.readmeless.pick(_, h, K.readmeless(t)) == K.readmeless(t) : List<&2, K.Item>}
  {==}

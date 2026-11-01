# proofs of laws/OldNameLeavesLicenseOut.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/OldNameLeavesLicenseOut.bend as Laws

def Laws.bare_drops_license(h, t, lic):
  %lic : {K.bare.pick(_, h, K.bare(t)) == K.bare(t) : List<&2, K.Item>}
  {==}

# proofs of laws/LicenseDirPasses.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/LicenseDirPasses.bend as Laws

def Laws.license_dir_passes(root, pre, out, none):
  %none : {K.made.lic(_, K.licensed(pre, out), root, pre, out)
    == K.made.placed(root, pre, out) : K.Walked}
  {==}

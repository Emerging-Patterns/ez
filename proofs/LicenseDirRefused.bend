# proofs of laws/LicenseDirRefused.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/LicenseDirRefused.bend as Laws

def Laws.license_dir_refused(root, pre, out, some):
  %some : {K.made.lic(_, K.licensed(pre, out), root, pre, out)
    == K.Refused{"ez: " ++ K.licensed(pre, out)
      ++ " is in a directory named license, which clashes with a LICENSE file"}
    : K.Walked}
  {==}

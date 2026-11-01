# proofs of laws/LicensedNames.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path
import ../laws/LicensedNames.bend as Laws

def Laws.licensed_names(pre, raw, _text, t, under):
  %under : {K.licensed.step(_, Path.join(pre, raw), _u => K.licensed(pre, t))
    == Path.join(pre, raw) : String}
  {==}

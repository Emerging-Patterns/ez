# proofs of laws/ForeignLicenseGoesAlong.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/ForeignLicenseGoesAlong.bend as Laws

def Laws.foreign_license_goes_along(_tree, _at, raw, text, lic, here):
  %here : {K.Hit{raw, text} <> K.license.put(_, K.beside(raw))
    == [K.Hit{raw, text}, K.Hit{K.beside(raw), lic}] : List<&2, K.Hit>}
  {==}

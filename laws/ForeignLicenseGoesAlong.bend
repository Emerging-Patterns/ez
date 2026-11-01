import Base
import ../src/pkg/pkg.bend as K

# LAW: a foreign body takes the LICENSE beside it along too, beside its own
# name in the package
law foreign_license_goes_along:
  for +tree: K.Tree
  for +at: String
  for +raw: String
  for text: String
  for lic: String
  for here: {K.Here{lic} == K.find(tree, K.beside(at)) : K.Look}
  {K.foreign.put(K.Here{text}, tree, at, raw)
    == [K.Hit{raw, text}, K.Hit{K.beside(raw), lic}] : List<&2, K.Hit>}

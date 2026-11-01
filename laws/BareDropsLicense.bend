import Base
import ../src/pkg/pkg.bend as K

# LAW: a package as bend named it before 2.0.27 leaves a LICENSE out
law bare_drops_license:
  for +h: K.Item
  for t: List<&2, K.Item>
  for lic: {True{} == K.file.lic(h) : Bool}
  {K.bare(h <> t) == K.bare(t) : List<&2, K.Item>}

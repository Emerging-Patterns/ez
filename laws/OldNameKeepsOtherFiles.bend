import Base
import ../src/pkg/pkg.bend as K

# LAW: and keeps every other file, in its place
law bare_keeps_sources:
  for +h: K.Item
  for t: List<&2, K.Item>
  for src: {False{} == K.file.lic(h) : Bool}
  {K.bare(h <> t) == h <> K.bare(t) : List<&2, K.Item>}

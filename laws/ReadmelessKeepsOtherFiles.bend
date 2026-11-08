import Base
import ../src/pkg/pkg.bend as K

# LAW: and keeps every other file, in its place, its LICENSE files included
law readmeless_keeps_others:
  for +h: K.Item
  for t: List<&2, K.Item>
  for other: {False{} == K.file.readme(h) : Bool}
  {K.readmeless(h <> t) == h <> K.readmeless(t) : List<&2, K.Item>}

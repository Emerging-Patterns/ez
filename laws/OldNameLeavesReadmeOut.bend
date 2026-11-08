import Base
import ../src/pkg/pkg.bend as K

# LAW: a package as bend named it before 2.0.40 leaves the README out
law readmeless_drops_readme:
  for +h: K.Item
  for t: List<&2, K.Item>
  for readme: {True{} == K.file.readme(h) : Bool}
  {K.readmeless(h <> t) == K.readmeless(t) : List<&2, K.Item>}

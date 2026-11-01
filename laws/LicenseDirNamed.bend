import Base
import ../src/pkg/pkg.bend as K
import ../src/pkg/path.bend as Path

# LAW: a found file placed under a directory named license is the one the
# check names
law licensed_names:
  for +pre: String
  for +raw: String
  for text: String
  for t: List<&2, K.Hit>
  for under: {True{} == K.license.under(Path.join(pre, raw)) : Bool}
  {K.licensed(pre, K.Hit{raw, text} <> t) == Path.join(pre, raw) : String}

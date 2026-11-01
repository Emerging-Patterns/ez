import Base
import ../src/pkg/path.bend as Path

# LAW: a module path that ends in `.bend` drops those five characters.
# The strip is the suffix and nothing else, so a name that merely holds
# those characters in the middle is left alone.
law unbend_ext:
  for +p: String
  {Path.unbend(p ++ ".bend") == p : String}

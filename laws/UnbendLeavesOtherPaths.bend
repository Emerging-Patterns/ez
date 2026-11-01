import Base
import ../src/pkg/path.bend as Path

# LAW: a path that does not end in `.bend` is its own module name. The strip
# is a strip and never a truncation of five characters off whatever it was
# handed.
law unbend_plain:
  for +p: String
  for e: {False{} == String.ends_with(p, ".bend") : Bool}
  {Path.unbend(p) == p : String}

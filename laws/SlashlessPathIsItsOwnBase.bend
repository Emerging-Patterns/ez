import Base
import ../src/pkg/path.bend as Path
import ./defs/Slashless.bend as D1

# LAW: so the base of a path with no separator is the path. The walk carries
# the one component it has, and nothing follows it.
law base_plain:
  for +p: String
  for e: {D1.slashless(p) == True{} : Bool}
  {Path.base(p) == p : String}

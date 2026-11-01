import Base
import ../src/pkg/path.bend as Path
import ./defs/Slashless.bend as D1

# LAW: and asking for the last component of such a path, or for more
# components than it has, gives all of it rather than the empty string a bad
# `take` would give. It holds for every such path and every count.
law tail_plain:
  for +p: String
  for q: Nat
  for e: {D1.slashless(p) == True{} : Bool}
  {Path.tail(p, 1n+q) == p : String}

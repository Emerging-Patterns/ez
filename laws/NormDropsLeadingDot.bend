import Base
import ../src/pkg/path.bend as Path

# LAW: so a leading `./` is the path without it, as long as the path did
# not already begin at the root. Gluing `./` onto a rooted path makes it
# relative, and that is a different path.
law norm_dot:
  for +p: String
  for e: {False{} == String.starts_with(p, "/") : Bool}
  {Path.norm("./" ++ p) == Path.norm(p) : String}

import Base
import ../src/pkg/path.bend as Path

# LAW: a path taken relative to nowhere is the path. An empty directory
# means the path is already where it should be, and `join` still
# normalises, so this is `norm` and not the raw text.
law join_bare:
  for +p: String
  {Path.join("", p) == Path.norm(p) : String}

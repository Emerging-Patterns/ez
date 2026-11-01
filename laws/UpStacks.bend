import Base
import ../src/pkg/path.bend as Path

# LAW: and a climb past a climb cancels nothing, because a climb is not a
# component to climb off. Two `..` in a row stay two: this is the edge that
# decides how far `pkg.place` re-roots a package, and folding them would
# re-root it one directory too shallow.
law up_stacks:
  for abs: Bool
  for t: List<&2, String>
  {Path.up(abs, ".." <> t) == ".." <> (".." <> t) : List<&2, String>}

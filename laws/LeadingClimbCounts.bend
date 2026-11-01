import Base
import ../src/pkg/path.bend as Path

# LAW: a leading climb is one climb more than what follows it. This is the
# count `pkg.place` re-roots by, so a path that climbs twice must count twice.
law ups_climb:
  for p: String
  {Path.ups("../" ++ p) == 1n+Path.ups(p) : Nat}

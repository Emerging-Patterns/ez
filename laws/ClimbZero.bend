import Base
import ../src/pkg/path.bend as Path

# LAW: climbing nothing leaves the path as `norm` left it. `pkg.place`
# climbs by a count, and a count of zero is a no-op on the directory.
law climb_zero:
  for +p: String
  {Path.climb(0n, p) == Path.norm(p) : String}

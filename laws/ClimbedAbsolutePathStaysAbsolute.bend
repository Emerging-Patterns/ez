import Base
import ../src/pkg/path.bend as Path

# LAW: and so re-rooting an absolute path leaves it absolute, however many
# directories it is climbed back off. `pkg.place` climbs by the deepest `..`
# any module of the package used, and this says that count cannot escape.
law climb_absolute:
  for n: Nat
  for +p: String
  for e: {True{} == String.starts_with(p, "/") : Bool}
  {String.starts_with(Path.climb(n, p), "/") == True{} : Bool}

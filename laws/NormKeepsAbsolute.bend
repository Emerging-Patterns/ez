import Base
import ../src/pkg/path.bend as Path
import ../src/add/world.bend as A

# LAW: so a path that began at the root normalises to a path that begins at
# the root. A climb at the root goes nowhere, which is `up.root`, and this is
# that fact stated where it bites: no count of `..` walks a normalisation off
# the top of an absolute path.
law norm_absolute:
  for +p: String
  for e: {True{} == String.starts_with(p, "/") : Bool}
  {String.starts_with(Path.norm(p), "/") == True{} : Bool}

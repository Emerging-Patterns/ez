import Base
import ../src/pkg/pkg.bend as K
import ../src/add/world.bend as A

# The header scan, which is what a package's file set is gathered from:
# which lines of a source file are modules, which are foreign bodies, and
# when the header has ended. A late import followed as if it were still
# in the header is a file the package does not hold, and a hub import
# followed as if it were a module is a walk that leaves the package.

# LAW: a spec that does not open `0x` is not a hub import. A relative
# path is a module of this package.
law hub_needs_0x:
  for +s: String
  for e: {False{} == String.starts_with(s, "0x") : Bool}
  {K.is_hub(s) == False{} : Bool}

import Base
import ../src/pkg/pkg.bend as K
import ../src/add/world.bend as A

# LAW: and a spec that holds no `/` is not one either. A `0x` name has
# no directory of its own, so the first `/` ends it; without one there
# is no package to name.
law hub_needs_slash:
  for +s: String
  for e: {False{} == String.contains(s, "/") : Bool}
  {K.is_hub(s) == False{} : Bool}

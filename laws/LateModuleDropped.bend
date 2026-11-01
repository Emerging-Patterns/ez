import Base
import ../src/pkg/pkg.bend as K

# LAW: a module named after the header has ended is dropped. The walk
# does not follow it.
law late_mod:
  for spec: String
  for mods: List<&2, String>
  for foreign: List<&2, String>
  {K.scan.mod(False{}, spec, mods, foreign)
    == K.Head{False{}, mods, foreign} : K.Head}

import Base
import ../src/pkg/pkg.bend as K

# LAW: a module named while the header is still open is kept
law header_mod:
  for spec: String
  for mods: List<&2, String>
  for foreign: List<&2, String>
  {K.scan.mod(True{}, spec, mods, foreign)
    == K.Head{True{}, spec <> mods, foreign} : K.Head}

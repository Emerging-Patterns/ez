import Base
import ../src/pkg/pkg.bend as K

# LAW: a body line ends the header, whatever it had gathered
law body_ends:
  for head: Bool
  for mods: List<&2, String>
  for foreign: List<&2, String>
  {K.scan.go(K.Head{head, mods, foreign}, K.SBody{})
    == K.Head{False{}, mods, foreign} : K.Head}

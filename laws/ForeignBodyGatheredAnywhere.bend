import Base
import ../src/pkg/pkg.bend as K

# LAW: a foreign body is gathered wherever it sits. It lives in a def's
# body, long after the header has ended, and the package still uploads
# it.
law foreign_keeps_head:
  for head: Bool
  for at: String
  for mods: List<&2, String>
  for foreign: List<&2, String>
  {K.scan.go(K.Head{head, mods, foreign}, K.SForeign{at})
    == K.Head{head, mods, at <> foreign} : K.Head}

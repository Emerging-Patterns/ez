# proofs of laws/ReadmeOverRefused.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/ReadmeOverRefused.bend as Laws

def Laws.readme_over_refused(_tree, entry, seen, out, queue, text, here, over):
  %here : {K.readme.put(_, K.readme(entry), entry, seen, out, queue)
    == K.Refused{"ez: " ++ K.readme(entry) ++ " cannot be published: it is over 65536 bytes, the most BendHub takes"}
    : K.Walked}
  %over : {K.readme.sized(_, K.readme(entry), entry, text, seen, out, queue)
    == K.Refused{"ez: " ++ K.readme(entry) ++ " cannot be published: it is over 65536 bytes, the most BendHub takes"}
    : K.Walked}
  {==}

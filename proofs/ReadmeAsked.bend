# proofs of laws/ReadmeAsked.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/ReadmeAsked.bend as Laws

def Laws.readme_asked(_tree, entry, seen, out, queue, unasked):
  %unasked : {K.readme.put(_, K.readme(entry), entry, seen, out, queue)
    == K.Asks{K.readme(entry)} : K.Walked}
  {==}

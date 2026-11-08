# proofs of laws/NoReadmeAsBefore.bend
import Base
import ../src/pkg/pkg.bend as K
import ../laws/NoReadmeAsBefore.bend as Laws

def Laws.no_readme_as_before(_tree, entry, seen, out, queue, none):
  %none : {K.readme.put(_, K.readme(entry), entry, seen, out, queue)
    == K.made(entry, K.State{seen, out, K.Going{}, queue}) : K.Walked}
  {==}

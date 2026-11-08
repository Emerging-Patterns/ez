# proofs of laws/StoppedWalkTakesNoReadme.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/check/eq.bend as Eq
import ../laws/StoppedWalkTakesNoReadme.bend as Laws

def Laws.stopped_walk_takes_no_readme(tree, entry, seen, out, stop, queue, stopped):
  match stop:
    case K.Going{}:
      Eq.bit.absurd(&2, {K.made.all(tree, entry, K.State{seen, out, K.Going{}, queue})
        == K.made(entry, K.State{seen, out, K.Going{}, queue}) : K.Walked}, stopped)
    case K.Missing{_at}:
      {==}
    case K.Climbs{_at}:
      {==}
    case K.Asking{_at}:
      {==}
    case K.Spent{}:
      {==}
    case K.Unnamed{_nv}:
      {==}

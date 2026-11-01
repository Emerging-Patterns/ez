# the names every part of a plan lays, in order
import Base
import ../../src/lock/lock.bend as L
import ../../src/fetch/plan.bend as FP

# the names every part lays, in order. Law vocabulary.
def puts(ms: List<&2, FP.Nm>) -> List<&2, L.Name>:
  match ms:
    case []:
      []
    case m <> t:
      match m:
        case FP.NmPut{nv, hash, _was}:
          L.Name{nv, hash} <> puts(t)
        case _:
          puts(t)

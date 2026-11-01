# whether every directory asked about splits along its path to where ez reads
# it
import Base
import ../../src/ws/workspace.bend as WWorkspace
import ../../src/ws/root.bend as RRoot

# whether every directory asked about, followed down by its path to where ez
# runs, is where ez runs
def splits(xs: List<&2, RRoot.Ask>, +here: List<&2, String>) -> Bool:
  match xs:
    case []:
      True{}
    case RRoot.Ask{ds, rs} <> tl:
      Bool.and(WWorkspace.segs.eq(List.append(&2, String, ds, rs), here), splits(tl, here))

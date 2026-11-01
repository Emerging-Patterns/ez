# proofs of laws/EzTreesAreNoLockRoots.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/pkg.bend as K
import ../src/lock/lock.bend as L
import ../laws/EzTreesAreNoLockRoots.bend as Laws

# `.ez/` is a prefix of anything appended to it, which `starts_append` holds,
# and that picks the arm that keeps nothing.
def Laws.root_skips_ez(p, text):
  Equal.cong(Bool, List<&2, String>,
    k => Bool.pick(List<&2, String>, k, [], L.specs(K.scan.mods(K.scan(text)))),
    String.starts_with(".ez/" ++ p, ".ez/"), True{}, Eq.starts_append(".ez/", p))

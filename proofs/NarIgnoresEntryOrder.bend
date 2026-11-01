# proofs of laws/NarIgnoresEntryOrder.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/sha/nar.bend as Nar
import ../laws/NarIgnoresEntryOrder.bend as Laws
import ../laws/SortIgnoresFileOrder.bend as L1
import ../laws/defs/LockInputs.bend as D1
import ./lemmas/FileInsertOrder.bend as M1

# `Nar.dir` sorts before it serializes, so this is pkg's `sort_perm` carried
# under `Nar.directory`
def Laws.nar_dir_order_free(ns, es, dis):
  Equal.cong(List<&2, K.Item>, String, ys => Nar.directory(ys),
    K.file.sort(D1.files.perm(ns, es)), K.file.sort(es),
    L1.sort_perm(ns, es, dis))

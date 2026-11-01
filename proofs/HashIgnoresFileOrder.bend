# proofs of laws/HashIgnoresFileOrder.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/share/sha.bend as Sha
import ../laws/HashIgnoresFileOrder.bend as Laws
import ../laws/ManifestIgnoresFileOrder.bend as L1
import ../laws/defs/LockInputs.bend as D1
import ./lemmas/FileInsertOrder.bend as M1

def Laws.hash_perm(ns, xs, dis):
  Equal.cong(String, String,
    m => "0x" ++ String.take(Sha.hex(m), 32n),
    K.manifest_of(D1.files.perm(ns, xs)), K.manifest_of(xs),
    L1.manifest_perm(ns, xs, dis))

# whether a package list names each hash at most once
import Base
import ../../src/lock/lock.bend as L

# whether a hash is none of the hashes a package list holds
def hash.fresh(+hash: String, ps: List<&2, L.Pack>) -> Bool:
  match ps:
    case []:
      True{}
    case Con{+h, t}:
      Bool.and(Bool.not(String.eq(hash, L.pack.hash(h))), hash.fresh(hash, t))

# whether a package list names each hash at most once. The walk's does: it
# passes over a hash it has resolved already.
def packs.distinct(ps: List<&2, L.Pack>) -> Bool:
  match ps:
    case []:
      True{}
    case Con{+h, +t}:
      Bool.and(hash.fresh(L.pack.hash(h), t), packs.distinct(t))

# The 0x hash of a file list with distinct paths depends only on its (path,
# sum) pairs, not on the order they were found in.
#
# A package is named by the sha256 of its manifest, so the manifest is the
# identity: two file sets that name the same files must render the same
# text, or the hash ez computes is not the hash the hub serves.
import Base
import ../src/pkg/pkg.bend as K
import ./defs/LockInputs.bend as D1

# LAW: and so the `0x` name a package is published under is the same name on
# every machine. This is what ez's content addressing rests on: a lock that
# pins `0x<hash>` pins the same files wherever it is read.
law hash_perm:
  for +ns: List<&2, Nat>
  for +xs: List<&2, K.Item>
  for +dis: {D1.files.distinct(xs) == True{} : Bool}
  {K.hash_of(D1.files.perm(ns, xs)) == K.hash_of(xs) : String}

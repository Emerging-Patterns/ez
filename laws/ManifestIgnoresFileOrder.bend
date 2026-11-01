import Base
import ../src/pkg/pkg.bend as K
import ./defs/LockInputs.bend as D1

# LAW: and so the manifest a package renders is the same text whatever order
# its files were found in. `manifest_of` sorts before it renders, so this
# follows from the law above.
law manifest_perm:
  for +ns: List<&2, Nat>
  for +xs: List<&2, K.Item>
  for +dis: {D1.files.distinct(xs) == True{} : Bool}
  {K.manifest_of(D1.files.perm(ns, xs)) == K.manifest_of(xs) : String}

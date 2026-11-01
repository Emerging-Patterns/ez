import Base
import ../src/pkg/pkg.bend as K
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L

# LAW: and the refusal names the package and the path, so the author knows
# which file to rename
law path_eq_named:
  for +hash: String
  for +src: L.Src
  for +at: String
  for +sum: String
  for +fs: List<&2, K.Item>
  for +rest: List<&2, L.Pack>
  for +e: {False{} == P.path.eqless(at) : Bool}
  {P.lockable.why(L.Pack{hash, src, K.Item{at, sum} <> fs} <> rest)
    == P.path.eq.why(hash, at) : String}

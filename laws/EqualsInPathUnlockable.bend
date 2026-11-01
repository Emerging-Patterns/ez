import Base
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L

# What the lock may hold. The pinned eztoml reader cuts a pair line at its
# first `=`, even inside a quoted key
# (https://github.com/Emerging-Patterns/eztoml/issues/24), so a file path
# holding one would read back as another path. The planner refuses such a
# lock rather than write one that does not read back.

# LAW: a package list with a file whose path holds `=` is not lockable,
# whatever else it holds
law path_eq_unlockable:
  for +hash: String
  for +src: L.Src
  for +at: String
  for +sum: String
  for +fs: List<&2, K.Item>
  for +rest: List<&2, L.Pack>
  for +ts: List<&2, M.Tool>
  for +hub: String
  for e: {False{} == P.path.eqless(at) : Bool}
  {P.lockable(L.Pack{hash, src, K.Item{at, sum} <> fs} <> rest, ts, hub) == False{}
    : Bool}

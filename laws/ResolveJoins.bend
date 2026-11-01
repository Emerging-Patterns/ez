import Base
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/ws/joint.bend as J

# LAW: and members resolved are joined as the ledgers they resolve to, every
# member imported by name a dependency after the root's own
law resolve_joins:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for dir: List<&2, String>
  for +rr: M.Manifest
  for +xs: List<&2, J.Member>
  for +ns: List<&2, M.Dep>
  for eu: {J.res.all(J.with.root(root, ms), J.with.root(root, ms), files) == J.Read{J.Member{dir, rr} <> xs}
    : J.Read}
  for en: {J.names.deps(J.with.root(root, ms), files) == J.Deps{ns} : J.Deps}
  {J.resolve(root, ms, files) == J.combine(J.with.deps(rr, List.append(&2, M.Dep, J.deps.of(rr), ns)), xs)
    : J.Joint}

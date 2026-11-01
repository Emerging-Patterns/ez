# proofs of laws/ResolvedMembersJoin.bend
import Base
import ../src/ledger/manifest.bend as M
import ../src/ws/joint.bend as J
import ../laws/ResolvedMembersJoin.bend as Laws

def Laws.resolve_joins(root, ms, files, dir, rr, xs, ns, eu, en):
  %Equal.sym(J.Read, J.res.all(J.with.root(root, ms), J.with.root(root, ms), files),
    J.Read{J.Member{dir, rr} <> xs}, eu)
    : {J.res.read(_, J.names.deps(J.with.root(root, ms), files))
      == J.combine(J.with.deps(rr, List.append(&2, M.Dep, J.deps.of(rr), ns)), xs) : J.Joint}
  %Equal.sym(J.Deps, J.names.deps(J.with.root(root, ms), files), J.Deps{ns}, en)
    : {J.res.named(J.Member{dir, rr} <> xs, _)
      == J.combine(J.with.deps(rr, List.append(&2, M.Dep, J.deps.of(rr), ns)), xs) : J.Joint}
  {==}

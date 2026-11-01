# proofs of laws/PublishedMemberImportedByName.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/pub/plan.bend as PP
import ../src/lock/lock.bend as L
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../laws/PublishedMemberImportedByName.bend as Laws

def Laws.member_dep_named(
  name,
  ms,
  self,
  files,
  dir,
  nn,
  ee,
  bb,
  hh,
  pa,
  pv,
  ds,
  ts,
  hash,
  root,
  fs,
  sums,
  ef,
  eo,
  nv,
  en,
  ew
):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds,
      ts}}}, ef)
    : {J.target(_, self, name, files) == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root, nv}}} : J.Res}
  %Equal.sym(Bool, WWorkspace.segs.eq(dir, self), False{}, eo)
    : {J.target.at(_, name, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}, dir, files, self) == J.Got{M.Dep{name,
        hash, J.entry.at(dir, ee), M.Member{root, nv}}} : J.Res}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.ByName{nv}, en)
    : {J.by.name(_, K.of(J.entry.at(dir, ee), files), name, J.entry.at(dir, ee)) == J.Got{M.Dep{name, hash,
        J.entry.at(dir, ee), M.Member{root, nv}}} : J.Res}
  %Equal.sym(K.Walked, K.of(J.entry.at(dir, ee), files), K.Walked{hash, root, fs, sums}, ew)
    : {J.walked(_, name, J.entry.at(dir, ee), nv) == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root,
        nv}}} : J.Res}
  {==}

def Laws.member_dep_unnamed(
  name,
  ms,
  self,
  files,
  dir,
  nn,
  ee,
  bb,
  hh,
  pa,
  pv,
  ds,
  ts,
  ef,
  eo,
  why,
  en
):
  %Equal.sym(Maybe<&2, J.Member>, J.named(ms, name), Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds,
      ts}}}, ef)
    : {J.target(_, self, name, files)
        == J.Bad{why ++ "; workspace member " ++ name ++ " is imported by the name ez publish would give it"} : J.Res}
  %Equal.sym(Bool, WWorkspace.segs.eq(dir, self), False{}, eo)
    : {J.target.at(_, name, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}, dir, files, self)
        == J.Bad{why ++ "; workspace member " ++ name ++ " is imported by the name ez publish would give it"} : J.Res}
  %Equal.sym(PP.Named, PP.naming(pa, pv), PP.Unnamed{why}, en)
    : {J.by.name(_, K.of(J.entry.at(dir, ee), files), name, J.entry.at(dir, ee))
        == J.Bad{why ++ "; workspace member " ++ name ++ " is imported by the name ez publish would give it"} : J.Res}
  {==}

def Laws.names_deps_named(dir, mm, xs, files, nv, dd, ds, en, eg, er):
  %Equal.sym(PP.Named, J.member.naming(J.Member{dir, mm}), PP.ByName{nv}, en)
    : {J.named.one(_, J.Member{dir, mm}, files, J.names.deps(xs, files)) == J.Deps{dd <> ds} : J.Deps}
  %Equal.sym(J.Res, J.member.dep(mm, dir, J.member.name(J.Member{dir, mm}), files), J.Got{dd}, eg)
    : {J.deps.cons(_, J.names.deps(xs, files)) == J.Deps{dd <> ds} : J.Deps}
  %Equal.sym(J.Deps, J.names.deps(xs, files), J.Deps{ds}, er)
    : {J.deps.cons(J.Got{dd}, _) == J.Deps{dd <> ds} : J.Deps}
  {==}

def Laws.names_deps_hashed(hd, xs, files, en):
  %Equal.sym(PP.Named, J.member.naming(hd), PP.ByHash{}, en)
    : {J.named.one(_, hd, files, J.names.deps(xs, files)) == J.names.deps(xs, files) : J.Deps}
  {==}

def Laws.member_name_recorded(_nn, hash, _entry, _path, nv, en):
  %Equal.sym(Bool, String.is_empty(nv), False{}, en)
    : {List.append(&2, L.Name, Bool.pick(List<&2, L.Name>, _, [], [L.Name{nv, hash}]), [])
      == [L.Name{nv, hash}] : List<&2, L.Name>}
  {==}

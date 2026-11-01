# A member whose ledger gives `publish-as` and `version` is imported by other
# members by the name `ez publish` would publish it under,
# `<publish-as>@<version>.0/...`, whether or not a section names it; a section
# naming a member whose name `ez publish` refuses is refused with its reason.
# `ez lock` resolves that name to the member's hash from the joint ledger,
# records the pair under `[names]` and lays `BEND_LIB/names/<name>@<version>`,
# and never asks the hub or reads the lock being rewritten for it. Editing
# such a member and running `ez lock` rewrites no source.
#
# also rests on: laws/LedgerNamesFirst.bend, laws/LockLaysItsNames.bend,
# laws/PlainLockWritesOnlyLock.bend, laws/ResolveJoins.bend,
# laws/ResolvedNotAsked.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/pub/plan.bend as PP
import ../src/lock/lock.bend as L
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J

# LAW: a member whose ledger gives `publish-as` and `version` is imported by
# the name `ez publish` would publish it under, `<publish-as>@<version>.0`,
# and the joint ledger records that name beside its hash
law member_dep_named:
  for +name: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for +dir: List<&2, String>
  for nn: String
  for +ee: String
  for bb: String
  for hh: String
  for pa: String
  for pv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for +hash: String
  for +root: String
  for fs: List<&2, K.Source>
  for sums: List<&2, K.Item>
  for ef: {J.named(ms, name) == Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}}}
    : Maybe<&2, J.Member>}
  for eo: {WWorkspace.segs.eq(dir, self) == False{} : Bool}
  for +nv: String
  for en: {PP.naming(pa, pv) == PP.ByName{nv} : PP.Named}
  for ew: {K.of(J.entry.at(dir, ee), files) == K.Walked{hash, root, fs, sums} : K.Walked}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root, nv}}} : J.Res}

# LAW: and a section naming a member whose name publish would refuse is
# refused with publish's reason
law member_dep_unnamed:
  for +name: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for +dir: List<&2, String>
  for nn: String
  for +ee: String
  for bb: String
  for hh: String
  for pa: String
  for pv: String
  for ds: List<&2, M.Dep>
  for ts: List<&2, M.Tool>
  for ef: {J.named(ms, name) == Some{J.Member{dir, M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}}}
    : Maybe<&2, J.Member>}
  for eo: {WWorkspace.segs.eq(dir, self) == False{} : Bool}
  for +why: String
  for en: {PP.naming(pa, pv) == PP.Unnamed{why} : PP.Named}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Bad{why ++ "; workspace member " ++ name ++ " is imported by the name ez publish would give it"} : J.Res}

# LAW: a member imported by name is a dependency of the joint ledger whether
# or not a section names it
law names_deps_named:
  for +dir: List<&2, String>
  for +mm: M.Manifest
  for +xs: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for +nv: String
  for +dd: M.Dep
  for +ds: List<&2, M.Dep>
  for en: {J.member.naming(J.Member{dir, mm}) == PP.ByName{nv} : PP.Named}
  for eg: {J.member.dep(mm, dir, J.member.name(J.Member{dir, mm}), files) == J.Got{dd} : J.Res}
  for er: {J.names.deps(xs, files) == J.Deps{ds} : J.Deps}
  {J.names.deps(J.Member{dir, mm} <> xs, files) == J.Deps{dd <> ds} : J.Deps}

# LAW: and a member imported by its hash adds none
law names_deps_hashed:
  for +hd: J.Member
  for +xs: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for en: {J.member.naming(hd) == PP.ByHash{} : PP.Named}
  {J.names.deps(hd <> xs, files) == J.names.deps(xs, files) : J.Deps}

# LAW: the lock's name table holds a named member's name with its hash, as it
# holds a name ez.toml records, so the lock resolves it from the ledger
# (`ledger_names_first`) and never asks the hub or the lock being rewritten
# for it (`resolved_not_asked`)
law member_name_recorded:
  for +nn: String
  for +hash: String
  for entry: String
  for path: String
  for +nv: String
  for en: {String.is_empty(nv) == False{} : Bool}
  {L.ledger.names.of([M.Dep{nn, hash, entry, M.Member{path, nv}}]) == [L.Name{nv, hash}] : List<&2, L.Name>}

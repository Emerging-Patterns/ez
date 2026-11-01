# A dependency section with `workspace = true` names the member whose
# `[package] name` is its key, and records no `hash`, no `entry` and no
# source; one that gives any of them, names no member, or names its own member
# is refused. Its hash is the `0x` name of that member's package walk from its
# entry over the committed tree, and no ledger records it. `ez lock` lays the
# walked tree of every member a section names under `BEND_LIB/<hash>`, and
# records the package of each one an import line names in the lock, as `kind =
# "member"` with its directory and entry.
#
# also rests on: laws/ResolvedMembersJoin.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/toml/toml.bend as T
import ../src/ledger/manifest.bend as M
import ../src/ledger/ignore.bend as I
import ../src/pub/plan.bend as PP
import ../src/lock/plan.bend as P
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../src/ws/up.bend as UUp

# ---------------------------------------------------------------------------
# a member as a dependency (laws/WorkspaceMemberDependency.bend)

# LAW: a member's section names the member whose `[package] name` is its
# key, and the joint ledger holds that member's package: its hash is the `0x`
# name of the walk from the member's entry over the committed files, with the
# entry it walked from, as a path from the root, and the directory the walk
# writes its paths from; one whose ledger names it neither way is imported by
# its hash
law member_dep_walked:
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
  for en: {PP.naming(pa, pv) == PP.ByHash{} : PP.Named}
  for ew: {K.of(J.entry.at(dir, ee), files) == K.Walked{hash, root, fs, sums} : K.Walked}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Got{M.Dep{name, hash, J.entry.at(dir, ee), M.Member{root, ""}}} : J.Res}

# LAW: the member a section names is the first whose `[package] name` is the
# section's key
law named_finds:
  for +dir: List<&2, String>
  for +name: String
  for +ee: String
  for +bb: String
  for +hh: String
  for +pa: String
  for +pv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +ms: List<&2, J.Member>
  {J.named(J.Member{dir, M.Manifest{name, ee, bb, hh, pa, pv, ds, ts}} <> ms, name)
    == Some{J.Member{dir, M.Manifest{name, ee, bb, hh, pa, pv, ds, ts}}} : Maybe<&2, J.Member>}

# LAW: and a member named otherwise is passed over
law named_skips:
  for +hd: J.Member
  for +ms: List<&2, J.Member>
  for +name: String
  for en: {String.eq(J.member.name(hd), name) == False{} : Bool}
  {J.named(hd <> ms, name) == J.named(ms, name) : Maybe<&2, J.Member>}

# LAW: a section naming no member is refused
law member_dep_unknown:
  for +name: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for ef: {J.named(ms, name) == None{} : Maybe<&2, J.Member>}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and no member's " ++
      "[package] is named " ++ name} : J.Res}

# LAW: and so is one naming the member it is written in
law member_dep_own:
  for +name: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for +dir: List<&2, String>
  for mm: M.Manifest
  for ef: {J.named(ms, name) == Some{J.Member{dir, mm}} : Maybe<&2, J.Member>}
  for eo: {WWorkspace.segs.eq(dir, self) == True{} : Bool}
  {J.dep.res(M.Dep{name, "", "", M.Member{"", ""}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and that member is itself"}
    : J.Res}

# LAW: a member's section records no hash: one that gives a hash is refused
law member_dep_hashed:
  for +name: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for eg: {String.is_empty(hash) == False{} : Bool}
  {J.dep.res(M.Dep{name, hash, entry, M.Member{path, nv}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
      " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}

# LAW: and no entry: one that gives an entry is refused
law member_dep_entried:
  for +name: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for eg: {String.is_empty(entry) == False{} : Bool}
  {J.dep.res(M.Dep{name, hash, entry, M.Member{path, nv}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
      " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}

# LAW: and no source: one that names a directory is refused
law member_dep_pathed:
  for +name: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for eg: {String.is_empty(path) == False{} : Bool}
  {J.dep.res(M.Dep{name, hash, entry, M.Member{path, nv}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
      " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}

# LAW: or a name to import it by
law member_dep_nv:
  for +name: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for eg: {String.is_empty(nv) == False{} : Bool}
  {J.dep.res(M.Dep{name, hash, entry, M.Member{path, nv}}, ms, self, files)
    == J.Bad{"ez: " ++ J.ledger.at(self) ++ " gives the workspace member " ++ name ++
      " a hash, an entry or a source; its section is `workspace = true` alone"} : J.Res}

# LAW: every other dependency is left as it is written: a hub one
law member_dep_hub:
  for +name: String
  for +hash: String
  for +entry: String
  for +nv: String
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  {J.dep.res(M.Dep{name, hash, entry, M.Hub{nv}}, ms, self, files)
    == J.Got{M.Dep{name, hash, entry, M.Hub{nv}}} : J.Res}

# LAW: and a git one
law member_dep_git:
  for +name: String
  for +hash: String
  for +entry: String
  for +url: String
  for +rev: String
  for +tag: String
  for +root: String
  for +nar: String
  for vend: Bool
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  {J.dep.res(M.Dep{name, hash, entry, M.Git{url, rev, tag, root, nar, vend}}, ms, self, files)
    == J.Got{M.Dep{name, hash, entry, M.Git{url, rev, tag, root, nar, vend}}} : J.Res}

# LAW: a refused section refuses its ledger's dependencies, the first in the
# order written
law deps_res_refuses:
  for +dd: M.Dep
  for +ds: List<&2, M.Dep>
  for +ms: List<&2, J.Member>
  for +self: List<&2, String>
  for +files: List<&2, K.Source>
  for +why: String
  for eb: {J.dep.res(dd, ms, self, files) == J.Bad{why} : J.Res}
  {J.deps.res(dd <> ds, ms, self, files) == J.Unmet{why} : J.Deps}

# LAW: a member whose dependencies are refused leaves the members unread
law res_one_refuses:
  for +dir: List<&2, String>
  for +mm: M.Manifest
  for +ms: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for rest: J.Read
  for +why: String
  for eu: {J.deps.res(J.deps.of(mm), ms, dir, files) == J.Unmet{why} : J.Deps}
  {J.res.one(J.Member{dir, mm}, ms, files, rest) == J.Unread{why} : J.Read}

# LAW: and so does any later member's refusal
law res_one_keeps_refusal:
  for +dir: List<&2, String>
  for +mm: M.Manifest
  for +ms: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for +ds: List<&2, M.Dep>
  for +why: String
  for eu: {J.deps.res(J.deps.of(mm), ms, dir, files) == J.Deps{ds} : J.Deps}
  {J.res.one(J.Member{dir, mm}, ms, files, J.Unread{why}) == J.Unread{why} : J.Read}

# LAW: members left unread leave nothing to lock: the joint ledger is refused
# with why
law resolve_refuses:
  for +root: M.Manifest
  for +ms: List<&2, J.Member>
  for +files: List<&2, K.Source>
  for +why: String
  for eu: {J.res.all(J.with.root(root, ms), J.with.root(root, ms), files) == J.Unread{why} : J.Read}
  {J.resolve(root, ms, files) == J.Clash{why} : J.Joint}

# LAW: the lock reads a member's package as its walk found it, fresh from the
# committed files: one answer, under the hash the joint ledger gives it
law seed_walked:
  for nn: String
  for +hash: String
  for +entry: String
  for +path: String
  for nv: String
  for +files: List<&2, K.Source>
  for hw: String
  for rw: String
  for +fs: List<&2, K.Source>
  for +sums: List<&2, K.Item>
  for ew: {K.of(entry, files) == K.Walked{hw, rw, fs, sums} : K.Walked}
  {J.seed(M.Dep{nn, hash, entry, M.Member{path, nv}}, files)
    == [W.Reply{W.Pkg{hash, L.Member{path, entry}, ""},
      W.Got{W.Clone{""}, K.manifest_of(sums), J.texts(sums, fs)}}] : List<&2, W.Reply>}

# LAW: an answer read fresh is one the lock lays, as a clone's is
law seed_cloned:
  for +hash: String
  for src: L.Src
  for hub: String
  for nar: String
  for manifest: String
  for ss: List<&2, String>
  {P.cloned([W.Reply{W.Pkg{hash, src, hub}, W.Got{W.Clone{nar}, manifest, ss}}]) == [hash]
    : List<&2, String>}

# LAW: the lock takes a member's dependency for a member's tree
law member_origin:
  for +nn: String
  for +hash: String
  for +entry: String
  for +path: String
  for +nv: String
  {L.ledger.origins([M.Dep{nn, hash, entry, M.Member{path, nv}}]) == [L.Origin{hash, L.Member{path, entry}}]
    : List<&2, L.Origin>}

# LAW: and judges its bytes alone, read fresh or from BEND_LIB
law member_judged:
  for path: String
  for entry: String
  for nar: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept.src(L.Member{path, entry}, W.Clone{nar}, hash, manifest, ss) == W.body(hash, manifest, ss)
    : W.Verdict}

# LAW: the same when it is read from BEND_LIB
law member_judged_lib:
  for path: String
  for entry: String
  for +hash: String
  for +manifest: String
  for +ss: List<&2, String>
  {W.accept.src(L.Member{path, entry}, W.Lib{}, hash, manifest, ss) == W.body(hash, manifest, ss)
    : W.Verdict}

# LAW: the lock writes a member's source as its directory and entry, and reads
# it back
law member_src_reads:
  for +path: String
  for +entry: String
  {L.src_of(L.src.pairs(L.Member{path, entry})) == L.Member{path, entry} : L.Src}

# LAW: a member is never vendored, so it is never laid under `.ez/lib`
law member_not_vended:
  for nn: String
  for hash: String
  for entry: String
  for path: String
  for nv: String
  for +ds: List<&2, M.Dep>
  {I.vendors(M.Dep{nn, hash, entry, M.Member{path, nv}} <> ds) == I.vendors(ds) : List<&2, String>}

# LAW: a fresh tree that passed and is not vendored is laid under BEND_LIB at
# its hash
law member_laid:
  for +hash: String
  for +vs: List<&2, String>
  for fs: List<&2, K.Item>
  for ss: List<&2, String>
  for +rest: List<&2, P.Effect>
  for ev: {L.seen.holds(vs, hash) == False{} : Bool}
  {P.lays([hash], vs, [W.Judged{hash, W.Ok{fs, ss}}], rest)
    == P.lay.verdict(W.Ok{fs, ss}, P.Cache{}, hash, rest) : List<&2, P.Effect>}

# LAW: a member's section is no ledger's to record anything in: the upgrade
# writes it back as it was written
law member_back_kept:
  for +nn: String
  for +hash: String
  for +entry: String
  for path: String
  for nv: String
  for joint: M.Dep
  {UUp.dep.back.at(M.Dep{nn, hash, entry, M.Member{path, nv}}, joint) == M.Dep{nn, hash, entry, M.Member{path, nv}}
    : M.Dep}

# LAW: a `[deps.<name>]` section with `workspace = true` is never one missing
# its hash
law member_not_missing:
  for n: String
  for +ps: List<&2, T.Kv>
  for ew: {M.flag(M.value(ps, "workspace")) == True{} : Bool}
  {M.missing.is(T.Sect{n, ps}) == False{} : Bool}

# ws/joint: the one ledger a workspace is locked from (EZ-WS-3). `ez lock` in
# a workspace writes one ez.lock.toml at the root, so it reads every member's
# ledger; rather than teach the lock planner a second kind of World, the
# members' ledgers are joined into one, and the lock planner runs on a World
# whose ledger is that one. Every law the lock planner has is about every
# World, so it holds of a workspace's lock as it does of a project's. The
# design is docs/rfc/ez-workspaces.md.
#
# The joint ledger is the root's `[package]` table with the dependencies and
# tools of the root and of every member, a member's relative path sources
# taken from the member's directory, as the root reads them. A name is one
# dependency, or one tool, across the workspace: the first declaration of it
# is the one the joint ledger holds, and every other must agree with it.
#
# A dependency section with `workspace = true` names another member by its
# `[package] name` (EZ-WS-5). Before the ledgers are joined, each such section
# is given the member's package: its hash, the `0x` name of the walk from the
# member's entry over the committed files, its entry as a path from the root,
# and the directory the walk writes its paths from. No ledger a person keeps
# records any of that; only the joint ledger the lock reads does.
import Base
import ../ledger/manifest.bend as M
import ../ledger/render.bend as Rend
import ../pkg/path.bend as P
import ../pkg/pkg.bend as K
import ../lock/lock.bend as L
import ../lock/world.bend as LW
import ../pub/plan.bend as PP
import ./workspace.bend as W

# one ez.toml git lists under the root, other than the root's own: its path
# from the root, and its text
type Found is Data:
  Found{path: String, text: String}

# a member's ledger, read: its directory and what it holds
type Member is Data:
  Member{dir: List<&2, String>, m: M.Manifest}

# what a workspace is locked from: as a project of its own, which is not a
# workspace; nothing, because something about the workspace was refused; or
# the joint ledger
type Joint is Data:
  Lone{}
  Clash{why: String}
  Joint{m: M.Manifest}

# ---------------------------------------------------------------------------
# a member's sources, as the root reads them

# a source read from a member's directory: a relative path joined to it, and
# a URL or an absolute path as it is (`P.anchor`, EZ-LED-8)
def source.at(+dir: String, src: M.Source) -> M.Source:
  match src:
    case M.Hub{nv}:
      M.Hub{nv}
    case M.Git{url, rev, tag, root, nar, vend}:
      M.Git{P.anchor(dir, url), rev, tag, root, nar, vend}
    case M.Member{path, named}:
      M.Member{path, named}

# a dependency read from a member's directory
def dep.at(+dir: String, dependency: M.Dep) -> M.Dep:
  M.Dep{nn, hh, ee, ss} = dependency
  M.Dep{nn, hh, ee, source.at(dir, ss)}

# every dependency read from a member's directory
def deps.at(+dir: String, ds: List<&2, M.Dep>) -> List<&2, M.Dep>:
  match ds:
    case []:
      []
    case hd <> tl:
      dep.at(dir, hd) <> deps.at(dir, tl)

# a tool read from a member's directory
def tool.at(+dir: String, pin: M.Tool) -> M.Tool:
  M.Tool{nn, ee, bb, ss} = pin
  M.Tool{nn, ee, bb, source.at(dir, ss)}

# every tool read from a member's directory
def tools.at(+dir: String, ts: List<&2, M.Tool>) -> List<&2, M.Tool>:
  match ts:
    case []:
      []
    case hd <> tl:
      tool.at(dir, hd) <> tools.at(dir, tl)

# every member's dependencies, in member order, each as the root reads it
def members.deps(ms: List<&2, Member>) -> List<&2, M.Dep>:
  match ms:
    case []:
      []
    case Member{ds, mm} <> tl:
      M.Manifest{_n, _e, _b, _h, _pa, _pv, xs, _ts} = mm
      List.append(&2, M.Dep, deps.at(W.segs.text(ds), xs), members.deps(tl))

# every member's tools, in member order, each as the root reads it
def members.tools(ms: List<&2, Member>) -> List<&2, M.Tool>:
  match ms:
    case []:
      []
    case Member{ds, mm} <> tl:
      M.Manifest{_n, _e, _b, _h, _pa, _pv, _xs, ts} = mm
      List.append(&2, M.Tool, tools.at(W.segs.text(ds), ts), members.tools(tl))

# the root's dependencies, then every member's
def all.deps(root: M.Manifest, ms: List<&2, Member>) -> List<&2, M.Dep>:
  M.Manifest{_n, _e, _b, _h, _pa, _pv, ds, _ts} = root
  List.append(&2, M.Dep, ds, members.deps(ms))

# the root's tools, then every member's
def all.tools(root: M.Manifest, ms: List<&2, Member>) -> List<&2, M.Tool>:
  M.Manifest{_n, _e, _b, _h, _pa, _pv, _ds, ts} = root
  List.append(&2, M.Tool, ts, members.tools(ms))

# ---------------------------------------------------------------------------
# one declaration per name

# every dependency, each name once, at its first declaration
def firsts(ds: List<&2, M.Dep>) -> List<&2, M.Dep>:
  match ds:
    case []:
      []
    case +hd <> tl:
      hd <> Rend.without(firsts(tl), M.dep.name(hd))

# a tool kept or dropped
def tools.without.put(hit: Bool, pin: M.Tool, rest: List<&2, M.Tool>) -> List<&2, M.Tool>:
  match hit:
    case True{}:
      rest
    case False{}:
      pin <> rest

# every tool but the one named
def tools.without(ts: List<&2, M.Tool>, +name: String) -> List<&2, M.Tool>:
  match ts:
    case []:
      []
    case +hd <> tl:
      tools.without.put(String.eq(M.tool.name(hd), name), hd, tools.without(tl, name))

# every tool, each name once, at its first declaration
def tools.firsts(ts: List<&2, M.Tool>) -> List<&2, M.Tool>:
  match ts:
    case []:
      []
    case +hd <> tl:
      hd <> tools.without(tools.firsts(tl), M.tool.name(hd))

# whether two bits are one
def bit.eq(aa: Bool, bb: Bool) -> Bool:
  match aa:
    case True{}:
      bb
    case False{}:
      Bool.not(bb)

# whether two sources are one
def source.eq(aa: M.Source, bb: M.Source) -> Bool:
  match aa:
    case M.Hub{an}:
      match bb:
        case M.Hub{bn}:
          String.eq(an, bn)
        case M.Git{_u, _r, _t, _o, _n, _v}:
          False{}
        case M.Member{_p, _m}:
          False{}
    case M.Git{au, ar, at, ao, an, av}:
      match bb:
        case M.Hub{_bn}:
          False{}
        case M.Git{bu, br, bt, bo, bn, bv}:
          Bool.and(Bool.and(Bool.and(String.eq(au, bu), String.eq(ar, br)),
            Bool.and(String.eq(at, bt), String.eq(ao, bo))),
            Bool.and(String.eq(an, bn), bit.eq(av, bv)))
        case M.Member{_p, _m}:
          False{}
    case M.Member{ap, am}:
      match bb:
        case M.Hub{_bn}:
          False{}
        case M.Git{_u, _r, _t, _o, _n, _v}:
          False{}
        case M.Member{bp, bm}:
          Bool.and(String.eq(ap, bp), String.eq(am, bm))

# whether two dependencies are one
def dep.eq(aa: M.Dep, bb: M.Dep) -> Bool:
  M.Dep{an, ah, ae, asrc} = aa
  M.Dep{bn, bh, be, bsrc} = bb
  Bool.and(Bool.and(String.eq(an, bn), String.eq(ah, bh)),
    Bool.and(String.eq(ae, be), source.eq(asrc, bsrc)))

# whether two tools are one
def tool.eq(aa: M.Tool, bb: M.Tool) -> Bool:
  M.Tool{an, ae, ab, asrc} = aa
  M.Tool{bn, be, bb2, bsrc} = bb
  Bool.and(Bool.and(String.eq(an, bn), String.eq(ae, be)),
    Bool.and(String.eq(ab, bb2), source.eq(asrc, bsrc)))

# whether every dependency of a list is the first declaration of its name in
# the whole list
def agree.go(ds: List<&2, M.Dep>, +all: List<&2, M.Dep>) -> Bool:
  match ds:
    case []:
      True{}
    case +hd <> tl:
      rest = agree.go(tl, all)
      Bool.and(dep.eq(hd, M.find(all, M.dep.name(hd))), rest)

# whether every declaration of a dependency agrees with the first
def agree(+ds: List<&2, M.Dep>) -> Bool:
  agree.go(ds, ds)

# the first dependency that does not agree with the first declaration of its
# name, "" for none
def clash.go(ds: List<&2, M.Dep>, +all: List<&2, M.Dep>) -> String:
  match ds:
    case []:
      ""
    case +hd <> tl:
      rest = clash.go(tl, all)
      Bool.pick(String, dep.eq(hd, M.find(all, M.dep.name(hd))), rest, M.dep.name(hd))

# whether every declaration of a tool agrees with the first
def tools.agree.go(ts: List<&2, M.Tool>, +all: List<&2, M.Tool>) -> Bool:
  match ts:
    case []:
      True{}
    case +hd <> tl:
      rest = tools.agree.go(tl, all)
      Bool.and(tool.eq(hd, M.tool.find(all, M.tool.name(hd))), rest)

# whether every declaration of a tool agrees with the first
def tools.agree(+ts: List<&2, M.Tool>) -> Bool:
  tools.agree.go(ts, ts)

# the first tool that does not agree with the first declaration of its name,
# "" for none
def tools.clash.go(ts: List<&2, M.Tool>, +all: List<&2, M.Tool>) -> String:
  match ts:
    case []:
      ""
    case +hd <> tl:
      rest = tools.clash.go(tl, all)
      Bool.pick(String, tool.eq(hd, M.tool.find(all, M.tool.name(hd))), rest, M.tool.name(hd))

# ---------------------------------------------------------------------------
# one pin per git source (EZ-WS-4)

# the pin a source is recorded at, once it is known whether it is the url
def pin.at(hit: Bool, src: M.Source, rest: M.Source) -> M.Source:
  match hit:
    case True{}:
      src
    case False{}:
      rest

# the first git source among the dependencies with this url, as the root
# reads it, or a hub source when there is none
def pin.of(ds: List<&2, M.Dep>, +url: String) -> M.Source:
  match ds:
    case []:
      M.Hub{""}
    case M.Dep{_n, _h, _e, +src} <> tl:
      rest = pin.of(tl, url)
      pin.at(String.eq(M.source.url(src), url), src, rest)

# whether two git sources are pinned alike: one commit and one tag
def pin.same(aa: M.Source, bb: M.Source) -> Bool:
  match aa:
    case M.Hub{_an}:
      True{}
    case M.Git{_au, ar, at, _ao, _an, _av}:
      match bb:
        case M.Hub{_bn}:
          True{}
        case M.Git{_bu, br, bt, _bo, _bn, _bv}:
          Bool.and(String.eq(ar, br), String.eq(at, bt))
        case M.Member{_bp, _bm}:
          True{}
    case M.Member{_ap, _am}:
      True{}

# whether every git dependency is pinned as the first declaration of its url
def pins.go(ds: List<&2, M.Dep>, +all: List<&2, M.Dep>) -> Bool:
  match ds:
    case []:
      True{}
    case M.Dep{_n, _h, _e, +src} <> tl:
      rest = pins.go(tl, all)
      Bool.and(pin.same(src, pin.of(all, M.source.url(src))), rest)

# whether every git source has one pin across the workspace
def pins(+ds: List<&2, M.Dep>) -> Bool:
  pins.go(ds, ds)

# the first git source pinned two ways, "" for none
def pins.clash.go(ds: List<&2, M.Dep>, +all: List<&2, M.Dep>) -> String:
  match ds:
    case []:
      ""
    case M.Dep{_n, _h, _e, +src} <> tl:
      rest = pins.clash.go(tl, all)
      Bool.pick(String, pin.same(src, pin.of(all, M.source.url(src))), rest, M.source.url(src))

# ---------------------------------------------------------------------------
# the hub

# whether a member's ledger names the root's hub: it names none, which is the
# root's, or the same one
def hub.one(+hub: String, mm: M.Manifest) -> Bool:
  M.Manifest{_n, _e, _b, +hh, _pa, _pv, _ds, _ts} = mm
  Bool.or(String.is_empty(hh), String.eq(hh, hub))

# whether every member names the root's hub
def hubs(+hub: String, ms: List<&2, Member>) -> Bool:
  match ms:
    case []:
      True{}
    case Member{_ds, mm} <> tl:
      rest = hubs(hub, tl)
      Bool.and(hub.one(hub, mm), rest)

# the first member naming another hub, "" for none
def hubs.other(+hub: String, ms: List<&2, Member>) -> String:
  match ms:
    case []:
      ""
    case Member{+ds, mm} <> tl:
      rest = hubs.other(hub, tl)
      Bool.pick(String, hub.one(hub, mm), rest, W.segs.text(ds))

# ---------------------------------------------------------------------------
# the joint ledger

# the root's hub
def root.hub(root: M.Manifest) -> String:
  M.Manifest{_n, _e, _b, hh, _pa, _pv, _ds, _ts} = root
  hh

# whether the members can be joined: every one names the root's hub, every
# declaration of a dependency and of a tool agrees with the first, and every
# git source is pinned at one commit and one tag
def ok(+root: M.Manifest, +ms: List<&2, Member>) -> Bool:
  Bool.and(hubs(root.hub(root), ms),
    Bool.and(Bool.and(agree(all.deps(root, ms)), pins(all.deps(root, ms))),
      tools.agree(all.tools(root, ms))))

# why the members cannot be joined
def why(+root: M.Manifest, +ms: List<&2, Member>) -> String:
  +other = hubs.other(root.hub(root), ms)
  +dep = clash.go(all.deps(root, ms), all.deps(root, ms))
  +pin = pins.clash.go(all.deps(root, ms), all.deps(root, ms))
  +tool = tools.clash.go(all.tools(root, ms), all.tools(root, ms))
  Bool.pick(String, String.is_empty(other),
    Bool.pick(String, String.is_empty(dep),
      Bool.pick(String, String.is_empty(pin),
        "ez: workspace members pin the tool " ++ tool ++ " differently",
        "ez: workspace members pin " ++ pin ++ " at different commits; " ++
          "move it for all of them with ez lock --upgrade --package"),
      "ez: workspace members depend on " ++ dep ++ " differently"),
    "ez: workspace member " ++ other ++ " names another hub than the root's")

# the joint ledger: the root's package, and every dependency and tool, each
# name at its first declaration
def joined(root: M.Manifest, +ms: List<&2, Member>) -> M.Manifest:
  M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts} = root
  M.Manifest{nn, ee, bb, hh, pa, pv,
    firsts(List.append(&2, M.Dep, ds, members.deps(ms))),
    tools.firsts(List.append(&2, M.Tool, ts, members.tools(ms)))}

# the members joined, once it is known whether they can be
def combine.go(fine: Bool, +root: M.Manifest, +ms: List<&2, Member>) -> Joint:
  match fine:
    case True{}:
      Joint{joined(root, ms)}
    case False{}:
      Clash{why(root, ms)}

# the root's ledger and every member's, joined, or why they cannot be
def combine(+root: M.Manifest, +ms: List<&2, Member>) -> Joint:
  combine.go(ok(root, ms), root, ms)

# the members' ledgers read, or why one could not be
type Read is Data:
  Unread{why: String}
  Read{ms: List<&2, Member>}

# ---------------------------------------------------------------------------
# a member as a dependency (EZ-WS-5)

# what a member's section resolves to: the dependency on the member's
# package, or why there is none
type Res is Data:
  Got{dep: M.Dep}
  Bad{why: String}

# a member's entry, as a path from the root
def entry.at(+dir: List<&2, String>, +entry: String) -> String:
  P.join(W.segs.text(dir), entry)

# the ledger a member's section is written in, as a path from the root
def ledger.at(+dir: List<&2, String>) -> String:
  P.join(W.segs.text(dir), "ez.toml")

# a member's `[package] name`
def member.name(mb: Member) -> String:
  Member{_dir, mm} = mb
  M.Manifest{nn, _e, _b, _h, _pa, _pv, _ds, _ts} = mm
  nn

# the member found, once it is known whether the head is it
def named.at(hit: Bool, hd: Member, rest: Maybe<&2, Member>) -> Maybe<&2, Member>:
  match hit:
    case True{}:
      Some{hd}
    case False{}:
      rest

# the first member whose `[package] name` is this one, or none
def named(ms: List<&2, Member>, +name: String) -> Maybe<&2, Member>:
  match ms:
    case []:
      None{}
    case +hd <> tl:
      rest = named(tl, name)
      named.at(String.eq(member.name(hd), name), hd, rest)

# a member's package, walked, as the dependency on it: the walk's hash, the
# entry it walked from, the directory it writes its paths from, and the name
# it is imported by, "" when it is imported by its hash
def walked(got: K.Walked, +name: String, +entry: String, +nv: String) -> Res:
  match got:
    case K.Walked{hash, root, _fs, _sums}:
      Got{M.Dep{name, hash, entry, M.Member{root, nv}}}
    case K.Asks{at}:
      Bad{"ez: workspace member " ++ name ++ " imports " ++ at ++ ", which git does not track"}
    case K.Refused{why}:
      Bad{why}

# a member's package, by the name `ez publish` would publish it under
# (EZ-WS-6): imported by that name when it has one, by its hash when its
# ledger gives neither `publish-as` nor `version`, and refused when it gives
# a name publish refuses
def by.name(named: PP.Named, got: K.Walked, +name: String, +entry: String) -> Res:
  match named:
    case PP.ByHash{}:
      walked(got, name, entry, "")
    case PP.ByName{nv}:
      walked(got, name, entry, nv)
    case PP.Unnamed{why}:
      Bad{why ++ "; workspace member " ++ name ++ " is imported by the name ez publish would give it"}

# a member's package, as the dependency on it
def member.dep(mm: M.Manifest, +dir: List<&2, String>, +name: String, +files: List<&2, K.Source>) -> Res:
  M.Manifest{_n, ee, _b, _h, pa, pv, _ds, _ts} = mm
  +entry = entry.at(dir, ee)
  by.name(PP.naming(pa, pv), K.of(entry, files), name, entry)

# the member a section names, once it is known whether it is the member
# that names it
def target.at(
  own: Bool,
  +name: String,
  mm: M.Manifest,
  +dir: List<&2, String>,
  +files: List<&2, K.Source>,
  +self: List<&2, String>
) -> Res:
  match own:
    case True{}:
      Bad{"ez: " ++ ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and that member is itself"}
    case False{}:
      member.dep(mm, dir, name, files)

# the member a section names, once it was looked for
def target(
  found: Maybe<&2, Member>,
  +self: List<&2, String>,
  +name: String,
  +files: List<&2, K.Source>
) -> Res:
  match found:
    case None{}:
      Bad{"ez: " ++ ledger.at(self) ++ " names " ++ name ++ " as a workspace member, and no member's " ++
        "[package] is named " ++ name}
    case Some{mb}:
      Member{+dir, mm} = mb
      target.at(W.segs.eq(dir, self), name, mm, dir, files, self)

# whether a member's section is `workspace = true` and nothing else
def bare(+hash: String, +entry: String, +path: String, +nv: String) -> Bool:
  Bool.and(Bool.and(String.is_empty(hash), String.is_empty(entry)),
    Bool.and(String.is_empty(path), String.is_empty(nv)))

# a member's section, once it is known whether it says nothing else
def section(
  plain: Bool,
  found: Maybe<&2, Member>,
  +self: List<&2, String>,
  +name: String,
  +files: List<&2, K.Source>
) -> Res:
  match plain:
    case True{}:
      target(found, self, name, files)
    case False{}:
      Bad{"ez: " ++ ledger.at(self) ++ " gives the workspace member " ++ name ++
        " a hash, an entry or a source; its section is `workspace = true` alone"}

# a dependency of the member at `self`, by its source: a member's section
# given the member's package, and any other as it is
def dep.res.src(
  src: M.Source,
  +name: String,
  +hash: String,
  +entry: String,
  +ms: List<&2, Member>,
  +self: List<&2, String>,
  +files: List<&2, K.Source>
) -> Res:
  match src:
    case M.Hub{nv}:
      Got{M.Dep{name, hash, entry, M.Hub{nv}}}
    case M.Git{url, rev, tag, root, nar, vend}:
      Got{M.Dep{name, hash, entry, M.Git{url, rev, tag, root, nar, vend}}}
    case M.Member{+path, +nv}:
      section(bare(hash, entry, path, nv), named(ms, name), self, name, files)

# a dependency of the member at `self`, resolved against every member
def dep.res(
  dependency: M.Dep,
  +ms: List<&2, Member>,
  +self: List<&2, String>,
  +files: List<&2, K.Source>
) -> Res:
  M.Dep{nn, hh, ee, src} = dependency
  dep.res.src(src, nn, hh, ee, ms, self, files)

# a member's dependencies resolved, or why one could not be
type Deps is Data:
  Deps{ds: List<&2, M.Dep>}
  Unmet{why: String}

# a dependency resolved in front of the rest, unless the rest could not be
def deps.cons(got: Res, rest: Deps) -> Deps:
  match got:
    case Bad{why}:
      Unmet{why}
    case Got{dd}:
      match rest:
        case Unmet{why}:
          Unmet{why}
        case Deps{ds}:
          Deps{dd <> ds}

# every dependency of the member at `self`, resolved, the first refusal in
# the order written winning
def deps.res(
  ds: List<&2, M.Dep>,
  +ms: List<&2, Member>,
  +self: List<&2, String>,
  +files: List<&2, K.Source>
) -> Deps:
  match ds:
    case []:
      Deps{[]}
    case hd <> tl:
      rest = deps.res(tl, ms, self, files)
      deps.cons(dep.res(hd, ms, self, files), rest)

# a member's ledger with these dependencies
def with.deps(mm: M.Manifest, ds: List<&2, M.Dep>) -> M.Manifest:
  M.Manifest{nn, ee, bb, hh, pa, pv, _ds, ts} = mm
  M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts}

# a member's ledger with its dependencies resolved, in front of the rest
def res.put(got: Deps, +dir: List<&2, String>, mm: M.Manifest, rest: Read) -> Read:
  match got:
    case Unmet{why}:
      Unread{why}
    case Deps{ds}:
      match rest:
        case Unread{why}:
          Unread{why}
        case Read{xs}:
          Read{Member{dir, with.deps(mm, ds)} <> xs}

# the dependencies a member's ledger records
def deps.of(mm: M.Manifest) -> List<&2, M.Dep>:
  M.Manifest{_n, _e, _b, _h, _pa, _pv, ds, _ts} = mm
  ds

# one member's ledger resolved against every member
def res.one(mb: Member, +ms: List<&2, Member>, +files: List<&2, K.Source>, rest: Read) -> Read:
  Member{+dir, +mm} = mb
  res.put(deps.res(deps.of(mm), ms, dir, files), dir, mm, rest)

# every member's ledger resolved against every member, `ms`
def res.all(xs: List<&2, Member>, +ms: List<&2, Member>, +files: List<&2, K.Source>) -> Read:
  match xs:
    case []:
      Read{[]}
    case hd <> tl:
      rest = res.all(tl, ms, files)
      res.one(hd, ms, files, rest)

# the name `ez publish` would publish a member under, or that it has none
def member.naming(mb: Member) -> PP.Named:
  Member{_dir, mm} = mb
  M.Manifest{_n, _e, _b, _h, pa, pv, _ds, _ts} = mm
  PP.naming(pa, pv)

# a member imported by name, as a dependency of the joint ledger, in front of
# the rest; any other member adds none
def named.one(named: PP.Named, mb: Member, +files: List<&2, K.Source>, rest: Deps) -> Deps:
  match named:
    case PP.ByHash{}:
      rest
    case PP.Unnamed{_why}:
      rest
    case PP.ByName{_nv}:
      Member{+dir, +mm} = mb
      deps.cons(member.dep(mm, dir, member.name(Member{dir, mm}), files), rest)

# every member imported by name, as a dependency of the joint ledger, whether
# or not a section names it, so that the lock resolves its name from the
# ledger and never puts it to the hub or to the lock being rewritten
# (EZ-WS-6). A member whose name publish refuses is imported by none, and
# adds none.
def names.deps(xs: List<&2, Member>, +files: List<&2, K.Source>) -> Deps:
  match xs:
    case []:
      Deps{[]}
    case +hd <> tl:
      rest = names.deps(tl, files)
      named.one(member.naming(hd), hd, files, rest)

# the root's ledger and the members', resolved, joined, the members imported
# by name after the root's own dependencies
def res.joint(xs: List<&2, Member>, +ns: List<&2, M.Dep>) -> Joint:
  match xs:
    case []:
      Clash{"ez: the workspace root has no ledger"}
    case Member{_dir, +root} <> ms:
      combine(with.deps(root, List.append(&2, M.Dep, deps.of(root), ns)), ms)

# the members imported by name, once every ledger was resolved
def res.named(xs: List<&2, Member>, got: Deps) -> Joint:
  match got:
    case Unmet{why}:
      Clash{why}
    case Deps{ns}:
      res.joint(xs, ns)

# the resolved ledgers joined, or why one could not be resolved
def res.read(rd: Read, got: Deps) -> Joint:
  match rd:
    case Unread{why}:
      Clash{why}
    case Read{xs}:
      res.named(xs, got)

# the root, as the member at the root's own directory, ahead of the members
def with.root(root: M.Manifest, ms: List<&2, Member>) -> List<&2, Member>:
  Member{[], root} <> ms

# the root's ledger and every member's, resolved and joined, or why they
# cannot be. The root is the member at the root's own directory, so a member
# may name it when it has a `[package]`, and its sections are resolved as a
# member's are.
def resolve(+root: M.Manifest, ms: List<&2, Member>, +files: List<&2, K.Source>) -> Joint:
  +all = with.root(root, ms)
  res.read(res.all(all, all, files), names.deps(all, files))

# ---------------------------------------------------------------------------
# the answers the lock reads a member's package from

# a file's text in a walk's files, "" when it holds none at that path
def text.at(fs: List<&2, K.Source>, +at: String) -> String:
  match fs:
    case []:
      ""
    case K.Source{+fa, ft} <> tl:
      rest = text.at(tl, at)
      Bool.pick(String, String.eq(fa, at), ft, rest)

# the texts of a walk's files, in its manifest's order
def texts(sums: List<&2, K.Item>, +fs: List<&2, K.Source>) -> List<&2, String>:
  match sums:
    case []:
      []
    case K.Item{at, _sum} <> tl:
      text.at(fs, at) <> texts(tl, fs)

# a member's package as the lock is to read it: fresh from the committed
# tree, as a clone arrives, so the lock lays it under BEND_LIB
def seed.walked(got: K.Walked, +hash: String, +path: String, +entry: String) -> List<&2, LW.Reply>:
  match got:
    case K.Walked{_h, _root, fs, +sums}:
      [LW.Reply{LW.Pkg{hash, L.Member{path, entry}, ""},
        LW.Got{LW.Clone{""}, K.manifest_of(sums), texts(sums, fs)}}]
    case K.Asks{_at}:
      []
    case K.Refused{_why}:
      []

# the answer for one dependency of the joint ledger, by its source: a
# member's package walked again from its entry, and nothing for any other
def seed.src(src: M.Source, +hash: String, +entry: String, +files: List<&2, K.Source>) -> List<&2, LW.Reply>:
  match src:
    case M.Hub{_nv}:
      []
    case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
      []
    case M.Member{path, _nv}:
      seed.walked(K.of(entry, files), hash, path, entry)

# the answer for one dependency of the joint ledger
def seed(dependency: M.Dep, +files: List<&2, K.Source>) -> List<&2, LW.Reply>:
  M.Dep{_n, hh, ee, src} = dependency
  seed.src(src, hh, ee, files)

# the answers for every member the joint ledger depends on
def seeds.of(ds: List<&2, M.Dep>, +files: List<&2, K.Source>) -> List<&2, LW.Reply>:
  match ds:
    case []:
      []
    case hd <> tl:
      List.append(&2, LW.Reply, seed(hd, files), seeds.of(tl, files))

# the answers the lock reads the members it depends on from: none for a
# project of its own, or for a workspace that cannot be joined
def seeds(jj: Joint, +files: List<&2, K.Source>) -> List<&2, LW.Reply>:
  match jj:
    case Lone{}:
      []
    case Clash{_why}:
      []
    case Joint{mm}:
      seeds.of(deps.of(mm), files)

# the committed files a listing names, as the walk takes them
def files.of(ls: List<&2, LW.Source>) -> List<&2, K.Source>:
  match ls:
    case []:
      []
    case LW.Source{at, text} <> tl:
      K.Source{at, text} <> files.of(tl)

# the committed files git listed, or none when it could not list them
def files(listing: LW.Listing) -> List<&2, K.Source>:
  match listing:
    case LW.Listed{ls}:
      files.of(ls)
    case LW.Unlisted{_why}:
      []

# ---------------------------------------------------------------------------
# from the texts git lists

# a ledger kept, when it is one under a directory
def ledgers.put(lg: Maybe<&2, W.Ledger>, rest: List<&2, W.Ledger>) -> List<&2, W.Ledger>:
  match lg:
    case None{}:
      rest
    case Some{ll}:
      ll <> rest

# every ledger git lists under the root, read for the member set
def ledgers(fs: List<&2, Found>) -> List<&2, W.Ledger>:
  match fs:
    case []:
      []
    case Found{+pp, +tt} <> tl:
      ledgers.put(W.ledger.of(pp, tt), ledgers(tl))

# a member read in front of the rest, unless the rest could not be read
def read.cons(+dir: List<&2, String>, rd: M.Read, rest: Read) -> Read:
  match rd:
    case M.Bad{why}:
      Unread{"ez: workspace member " ++ W.segs.text(dir) ++ " has an ez.toml that does not parse: " ++ why}
    case M.Good{mm}:
      match rest:
        case Unread{why}:
          Unread{why}
        case Read{ms}:
          Read{Member{dir, mm} <> ms}

# a ledger git listed, kept when it is a member's
def read.pick(hit: Bool, +dir: List<&2, String>, +text: String, rest: Read) -> Read:
  match hit:
    case True{}:
      read.cons(dir, M.parse(text), rest)
    case False{}:
      rest

# a ledger git listed, when it is one under a directory
def read.one(lg: Maybe<&2, W.Ledger>, +dirs: List<&2, List<&2, String>>, +text: String, rest: Read) -> Read:
  match lg:
    case None{}:
      rest
    case Some{ll}:
      +dir = W.ledger.dir(ll)
      read.pick(W.has(dirs, dir), dir, text, rest)

# every member's ledger, read in the order git listed them
def read.all(fs: List<&2, Found>, +dirs: List<&2, List<&2, String>>) -> Read:
  match fs:
    case []:
      Read{[]}
    case Found{+pp, +tt} <> tl:
      rest = read.all(tl, dirs)
      read.one(W.ledger.of(pp, tt), dirs, tt, rest)

# the members joined with the root, once each was read and every member's
# section resolved
def joint.read(rd: Read, +root: M.Manifest, +files: List<&2, K.Source>) -> Joint:
  match rd:
    case Unread{why}:
      Clash{why}
    case Read{ms}:
      resolve(root, ms, files)

# the members joined with the root, once the root's ledger was read
def joint.root(
  rd: M.Read,
  +fs: List<&2, Found>,
  +dirs: List<&2, List<&2, String>>,
  +files: List<&2, K.Source>
) -> Joint:
  match rd:
    case M.Bad{why}:
      Clash{why}
    case M.Good{root}:
      joint.read(read.all(fs, dirs), root, files)

# the members joined, once the member set is known
def joint.members(
  ms: W.Members,
  +text: String,
  +fs: List<&2, Found>,
  +files: List<&2, K.Source>
) -> Joint:
  match ms:
    case W.Refused{why}:
      Clash{why}
    case W.Members{_root, dirs}:
      joint.root(M.parse(text), fs, dirs, files)

# what the root's `[workspace]` table says, against the ledgers git lists
def joint.spec(rd: W.Read, +text: String, +fs: List<&2, Found>, +files: List<&2, K.Source>) -> Joint:
  match rd:
    case W.Lone{}:
      Lone{}
    case W.Bad{why}:
      Clash{why}
    case W.Root{+spec}:
      joint.members(W.members(spec, W.root.of(text), ledgers(fs)), text, fs, files)

# what a project is locked from: its own ledger when it is no workspace root,
# the joint ledger of the root and every member when it is one, or why there
# is none. `text` is the root's ez.toml, `fs` every other ez.toml git lists
# under it, and `files` the committed `.bend` files a member's package is
# walked over.
def joint(+text: String, +fs: List<&2, Found>, +files: List<&2, K.Source>) -> Joint:
  joint.spec(W.spec.of(text), text, fs, files)

# the ledger text the lock planner reads: the joint ledger, rendered
def joint.text(+jj: Joint, +own: Maybe<&2, String>) -> Maybe<&2, String>:
  match jj:
    case Lone{}:
      own
    case Clash{_why}:
      own
    case Joint{mm}:
      Some{Rend.show(mm)}

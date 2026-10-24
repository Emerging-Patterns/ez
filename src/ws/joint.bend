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
import Base
import ../ledger/manifest.bend as M
import ../ledger/render.bend as Rend
import ../pkg/path.bend as P
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
    case M.Git{au, ar, at, ao, an, av}:
      match bb:
        case M.Hub{_bn}:
          False{}
        case M.Git{bu, br, bt, bo, bn, bv}:
          Bool.and(Bool.and(Bool.and(String.eq(au, bu), String.eq(ar, br)),
            Bool.and(String.eq(at, bt), String.eq(ao, bo))),
            Bool.and(String.eq(an, bn), bit.eq(av, bv)))

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

# whether the members can be joined: every one names the root's hub, and
# every declaration of a dependency and of a tool agrees with the first
def ok(+root: M.Manifest, +ms: List<&2, Member>) -> Bool:
  Bool.and(hubs(root.hub(root), ms),
    Bool.and(agree(all.deps(root, ms)), tools.agree(all.tools(root, ms))))

# why the members cannot be joined
def why(+root: M.Manifest, +ms: List<&2, Member>) -> String:
  +other = hubs.other(root.hub(root), ms)
  +dep = clash.go(all.deps(root, ms), all.deps(root, ms))
  +tool = tools.clash.go(all.tools(root, ms), all.tools(root, ms))
  Bool.pick(String, String.is_empty(other),
    Bool.pick(String, String.is_empty(dep),
      "ez: workspace members pin the tool " ++ tool ++ " differently",
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

# the members' ledgers read, or why one could not be
type Read is Data:
  Unread{why: String}
  Read{ms: List<&2, Member>}

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

# the members joined with the root, once each was read
def joint.read(rd: Read, +root: M.Manifest) -> Joint:
  match rd:
    case Unread{why}:
      Clash{why}
    case Read{ms}:
      combine(root, ms)

# the members joined with the root, once the root's ledger was read
def joint.root(rd: M.Read, +fs: List<&2, Found>, +dirs: List<&2, List<&2, String>>) -> Joint:
  match rd:
    case M.Bad{why}:
      Clash{why}
    case M.Good{root}:
      joint.read(read.all(fs, dirs), root)

# the members joined, once the member set is known
def joint.members(
  ms: W.Members,
  +text: String,
  +fs: List<&2, Found>
) -> Joint:
  match ms:
    case W.Refused{why}:
      Clash{why}
    case W.Members{_root, dirs}:
      joint.root(M.parse(text), fs, dirs)

# what the root's `[workspace]` table says, against the ledgers git lists
def joint.spec(rd: W.Read, +text: String, +fs: List<&2, Found>) -> Joint:
  match rd:
    case W.Lone{}:
      Lone{}
    case W.Bad{why}:
      Clash{why}
    case W.Root{+spec}:
      joint.members(W.members(spec, W.root.of(text), ledgers(fs)), text, fs)

# what a project is locked from: its own ledger when it is no workspace root,
# the joint ledger of the root and every member when it is one, or why there
# is none. `text` is the root's ez.toml and `fs` every other ez.toml git
# lists under it.
def joint(+text: String, +fs: List<&2, Found>) -> Joint:
  joint.spec(W.spec.of(text), text, fs)

# the ledger text the lock planner reads: the joint ledger, rendered
def joint.text(+jj: Joint, +own: Maybe<&2, String>) -> Maybe<&2, String>:
  match jj:
    case Lone{}:
      own
    case Clash{_why}:
      own
    case Joint{mm}:
      Some{Rend.show(mm)}

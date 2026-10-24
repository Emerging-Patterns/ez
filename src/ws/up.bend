# ws/up: `ez lock --upgrade` at a workspace root (EZ-WS-4). The upgrade is
# planned, as the lock is, on the joint ledger (ws/joint.bend), so a source a
# name declares moves once for the whole workspace. What it writes back is
# not the joint ledger, which no file holds: the one write of ez.toml the
# upgrade plans is replaced by a write of every ledger that declares a moved
# name, the root's and each member's, each dependency and tool taking its new
# pin from the joint ledger the upgrade leaves while keeping the source as
# that ledger records it, relative to its own directory. Every other effect of
# the plan is kept as it was.
import Base
import ../ledger/manifest.bend as M
import ../ledger/render.bend as Rend
import ../toml/toml.bend as T
import ../lock/world.bend as LW
import ../lock/plan.bend as LP
import ./workspace.bend as W
import ./joint.bend as J

# what the write-back needs: nothing, for a project of its own, or the root's
# ledger text, what its `[workspace]` table says, and every other ez.toml git
# lists under the root
type Back is Data:
  Alone{}
  Back{text: String, spec: W.Spec, found: List<&2, J.Found>}

# ---------------------------------------------------------------------------
# a pin moved back into a ledger

# a source with the pin the joint ledger now gives it: the joint's commit,
# tag, root and narHash, and this ledger's own url and vendor bit
def source.back(own: M.Source, joint: M.Source) -> M.Source:
  match own:
    case M.Hub{nv}:
      M.Hub{nv}
    case M.Git{url, _rev, _tag, _root, _nar, vend}:
      match joint:
        case M.Hub{_jn}:
          M.Git{url, _rev, _tag, _root, _nar, vend}
        case M.Git{_ju, jr, jt, jo, jn, _jv}:
          M.Git{url, jr, jt, jo, jn, vend}
        case M.Member{_jp, _jm}:
          M.Git{url, _rev, _tag, _root, _nar, vend}
    case M.Member{path, named}:
      M.Member{path, named}

# a dependency with the pin the joint ledger gives its name, by its own
# source: a workspace member's section is kept as it is written, since the
# hash and entry the joint ledger gives it are no ledger's to record
def dep.back.src(own: M.Source, +nn: String, +hh: String, +ee: String, joint: M.Dep) -> M.Dep:
  match own:
    case M.Member{path, nv}:
      M.Dep{nn, hh, ee, M.Member{path, nv}}
    case M.Hub{nv}:
      M.Dep{_jn, jh, je, js} = joint
      M.Dep{nn, jh, je, source.back(M.Hub{nv}, js)}
    case M.Git{url, rev, tag, root, nar, vend}:
      M.Dep{_jn, jh, je, js} = joint
      M.Dep{nn, jh, je, source.back(M.Git{url, rev, tag, root, nar, vend}, js)}

# a dependency with the pin the joint ledger gives its name
def dep.back.at(own: M.Dep, joint: M.Dep) -> M.Dep:
  M.Dep{nn, hh, ee, os} = own
  dep.back.src(os, nn, hh, ee, joint)

# a dependency of a ledger, after the upgrade
def dep.back(+own: M.Dep, +js: List<&2, M.Dep>) -> M.Dep:
  dep.back.at(own, M.find(js, M.dep.name(own)))

# every dependency of a ledger, after the upgrade
def deps.back(ds: List<&2, M.Dep>, +js: List<&2, M.Dep>) -> List<&2, M.Dep>:
  match ds:
    case []:
      []
    case +hd <> tl:
      dep.back(hd, js) <> deps.back(tl, js)

# a tool with the pin the joint ledger gives its name
def tool.back.at(own: M.Tool, joint: M.Tool) -> M.Tool:
  M.Tool{nn, ee, bb, os} = own
  M.Tool{_jn, _je, _jb, js} = joint
  M.Tool{nn, ee, bb, source.back(os, js)}

# a tool of a ledger, after the upgrade
def tool.back(+own: M.Tool, +ts: List<&2, M.Tool>) -> M.Tool:
  tool.back.at(own, M.tool.find(ts, M.tool.name(own)))

# every tool of a ledger, after the upgrade
def tools.back(ts: List<&2, M.Tool>, +js: List<&2, M.Tool>) -> List<&2, M.Tool>:
  match ts:
    case []:
      []
    case +hd <> tl:
      tool.back(hd, js) <> tools.back(tl, js)

# a ledger after the upgrade, every pin taken from the joint ledger
def ledger.back(mm: M.Manifest, joint: M.Manifest) -> M.Manifest:
  M.Manifest{nn, ee, bb, hh, pa, pv, ds, ts} = mm
  M.Manifest{_jn, _je, _jb, _jh, _jpa, _jpv, +jd, +jt} = joint
  M.Manifest{nn, ee, bb, hh, pa, pv, deps.back(ds, jd), tools.back(ts, jt)}

# ---------------------------------------------------------------------------
# the root's ledger, written back with its `[workspace]` table

# texts written as a TOML array of strings
def array.items(ts: List<&2, String>) -> String:
  match ts:
    case []:
      ""
    case +hd <> []:
      T.quote(hd)
    case +hd <> tl:
      T.quote(hd) ++ ", " ++ array.items(tl)

# every entry as it was written
def entries.text(es: List<&2, W.Entry>) -> List<&2, String>:
  match es:
    case []:
      []
    case hd <> tl:
      W.entry.text(hd) <> entries.text(tl)

# every path as it was written
def paths.text(ps: List<&2, List<&2, String>>) -> List<&2, String>:
  match ps:
    case []:
      []
    case hd <> tl:
      W.segs.text(hd) <> paths.text(tl)

# the `[workspace]` table, as it says what it says
def spec.text(spec: W.Spec) -> String:
  W.Spec{es, ex} = spec
  "[workspace]\nmembers = [" ++ array.items(entries.text(es)) ++ "]\nexclude = [" ++
    array.items(paths.text(ex)) ++ "]\n"

# the root's ledger as a file: its package table when it has one, which a
# virtual root does not, its dependencies and tools, and its `[workspace]`
def root.text(+mm: M.Manifest, +spec: W.Spec, +root: W.Root) -> String:
  +body = Rend.text(mm)
  T.normal(Bool.pick(String, W.root.member(root), body, String.drop(body, 10n)) ++ spec.text(spec))

# ---------------------------------------------------------------------------
# the writes

# a ledger written back when the upgrade changed what it holds, and left as
# it was otherwise
def write.if(+mm: M.Manifest, +joint: M.Manifest, +at: String, +text: String) -> List<&2, LP.Effect>:
  Bool.pick(List<&2, LP.Effect>, String.eq(Rend.show(mm), Rend.show(ledger.back(mm, joint))),
    [], [LP.Write{at, text}])

# a member's ledger, written back at its directory's ez.toml
def member.write(rd: M.Read, +ds: List<&2, String>, +joint: M.Manifest) -> List<&2, LP.Effect>:
  match rd:
    case M.Bad{_why}:
      []
    case M.Good{+mm}:
      write.if(mm, joint, W.segs.text(ds) ++ "/ez.toml", Rend.show(ledger.back(mm, joint)))

# a member's ledger written back, or, for another's, nothing
def found.pick(hit: Bool, +text: String, +ds: List<&2, String>, +joint: M.Manifest) -> List<&2, LP.Effect>:
  match hit:
    case True{}:
      member.write(M.parse(text), ds, joint)
    case False{}:
      []

# one ez.toml git listed, written back when it is a member's
def found.write(
  lg: Maybe<&2, W.Ledger>,
  +text: String,
  +dirs: List<&2, List<&2, String>>,
  +joint: M.Manifest
) -> List<&2, LP.Effect>:
  match lg:
    case None{}:
      []
    case Some{ll}:
      +ds = W.ledger.dir(ll)
      found.pick(W.has(dirs, ds), text, ds, joint)

# every member's ledger the upgrade changed, written back
def members.write(
  fs: List<&2, J.Found>,
  +dirs: List<&2, List<&2, String>>,
  +joint: M.Manifest
) -> List<&2, LP.Effect>:
  match fs:
    case []:
      []
    case J.Found{+pp, +tt} <> tl:
      List.append(&2, LP.Effect, found.write(W.ledger.of(pp, tt), tt, dirs, joint),
        members.write(tl, dirs, joint))

# the root's ledger, written back when the upgrade changed it
def root.write(rd: M.Read, +spec: W.Spec, +root: W.Root, +joint: M.Manifest) -> List<&2, LP.Effect>:
  match rd:
    case M.Bad{_why}:
      []
    case M.Good{+mm}:
      write.if(mm, joint, "ez.toml", root.text(ledger.back(mm, joint), spec, root))

# every ledger the upgrade changed, the root's first, once the member set is
# known
def writes.members(
  ms: W.Members,
  +text: String,
  +spec: W.Spec,
  +fs: List<&2, J.Found>,
  +joint: M.Manifest
) -> List<&2, LP.Effect>:
  match ms:
    case W.Refused{_why}:
      []
    case W.Members{_root, +dirs}:
      List.append(&2, LP.Effect, root.write(M.parse(text), spec, W.root.of(text), joint),
        members.write(fs, dirs, joint))

# every ledger the upgrade changed, once the joint ledger it leaves was read
def writes.joint(joint: M.Read, +text: String, +spec: W.Spec, +fs: List<&2, J.Found>) -> List<&2, LP.Effect>:
  match joint:
    case M.Bad{_why}:
      []
    case M.Good{+jm}:
      writes.members(W.members(spec, W.root.of(text), J.ledgers(fs)), text, spec, fs, jm)

# every ledger the upgrade changed, from the joint ledger it leaves
def writes(back: Back, joint: M.Read) -> List<&2, LP.Effect>:
  match back:
    case Alone{}:
      []
    case Back{+text, +spec, +fs}:
      writes.joint(joint, text, spec, fs)

# a write kept, or, when it is of ez.toml, the ledgers' in its place
def effect.write(
  hit: Bool,
  at: String,
  text: String,
  ws: List<&2, LP.Effect>,
  rest: List<&2, LP.Effect>
) -> List<&2, LP.Effect>:
  match hit:
    case True{}:
      List.append(&2, LP.Effect, ws, rest)
    case False{}:
      LP.Write{at, text} <> rest

# one effect of the plan: the write of ez.toml replaced by the ledgers'
def effect.back(effect: LP.Effect, +ws: List<&2, LP.Effect>, rest: List<&2, LP.Effect>) -> List<&2, LP.Effect>:
  match effect:
    case LP.Write{+at, text}:
      effect.write(String.eq(at, "ez.toml"), at, text, ws, rest)
    case LP.Lay{pl, hash, files}:
      LP.Lay{pl, hash, files} <> rest
    case LP.Drop{hash}:
      LP.Drop{hash} <> rest
    case LP.Say{text}:
      LP.Say{text} <> rest
    case LP.Name{nv, hash}:
      LP.Name{nv, hash} <> rest

# every effect, with the write of ez.toml replaced
def effects.back(es: List<&2, LP.Effect>, +ws: List<&2, LP.Effect>) -> List<&2, LP.Effect>:
  match es:
    case []:
      []
    case hd <> tl:
      rest = effects.back(tl, ws)
      effect.back(hd, ws, rest)

# the plan with its write of ez.toml replaced by the ledgers'
def plan.back(pl: LP.Plan, +ws: List<&2, LP.Effect>) -> LP.Plan:
  LP.Plan{es, outcome} = pl
  LP.Plan{effects.back(es, ws), outcome}

# what `ez lock` runs at a workspace root, under `--upgrade` or not
def plan.at(up: Bool, +back: Back, +world: LW.World) -> LP.Plan:
  match up:
    case True{}:
      plan.back(LP.plan(world), writes(back, LP.ledger.next(world)))
    case False{}:
      LP.plan(world)

# what `ez lock` runs: for a project of its own, the plan the lock planner
# makes; at a workspace root, the plan it makes on the joint ledger, with,
# under `--upgrade`, every ledger the upgrade changed written back in place of
# the joint one. A plain lock writes no ledger, so its plan is as it was.
def plan(back: Back, +world: LW.World) -> LP.Plan:
  match back:
    case Alone{}:
      LP.plan(world)
    case Back{+text, +spec, +fs}:
      plan.at(LW.args.upgrade(world), Back{text, spec, fs}, world)

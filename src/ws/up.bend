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
import ../pkg/pkg.bend as K
import ./workspace.bend as W
import ./joint.bend as J
import ./moved.bend as Mv

# what the write-back needs: nothing, for a project of its own, or the root's
# ledger text, what its `[workspace]` table says, every other ez.toml git
# lists under the root, and the text of the lock being rewritten, "" for
# none, which records each member's hash before it moved (EZ-WS-7)
type Back is Data:
  Alone{}
  Back{text: String, spec: W.Spec, found: List<&2, J.Found>, lock: String}

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
    case Back{+text, +spec, +fs, _lock}:
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

# ---------------------------------------------------------------------------
# members imported by their hash (EZ-WS-7)

# the World an upgrade plans on, and the files it rewrites
type Up is Data:
  Up{world: LW.World, edits: List<&2, LP.Effect>}

# the committed files a World lists
def files.of(world: LW.World) -> List<&2, K.Source>:
  LW.World{_args, _ledger, listing, _replies, _ups} = world
  J.files(listing)

# an upgrade at a workspace root, once its moves are known: the World with
# every committed file rewritten by them, and the writes of the files they
# change
def up.moves(+ms: List<&2, Mv.Shift>, +text: String, +fs: List<&2, J.Found>, +world: LW.World) -> Up:
  +files = files.of(world)
  +moved = Mv.rewrite(Mv.swaps(ms), files)
  Up{Mv.world.moved(J.joint(text, fs, moved), moved, world), Mv.edits(Mv.swaps(ms), files)}

# an upgrade at a workspace root: every member it moves (ws/moved.bend), its
# import lines rewritten, until none moves further
def up.of(+text: String, +fs: List<&2, J.Found>, +lock: String, +world: LW.World) -> Up:
  up.moves(Mv.cascade(Mv.ctx(text, fs, files.of(world), lock, LW.args.only(world))), text, fs, world)

# the World an upgrade plans on
def up.world(got: Up) -> LW.World:
  Up{w2, _eds} = got
  w2

# the World `ez lock` plans on at a workspace root: a plain lock's as it is,
# and an upgrade's with every moved member's import lines rewritten
def world.at(up: Bool, +text: String, +fs: List<&2, J.Found>, +lock: String, +world: LW.World) -> LW.World:
  match up:
    case True{}:
      up.world(up.of(text, fs, lock, world))
    case False{}:
      world

# the World `ez lock` plans on
def plans.on(back: Back, +world: LW.World) -> LW.World:
  match back:
    case Alone{}:
      world
    case Back{+text, _spec, +fs, +lock}:
      world.at(LW.args.upgrade(world), text, fs, lock, world)

# why a plain lock at a workspace root refuses before it asks anything: a
# committed line names the hash the lock being rewritten records for a member
# that has moved since. "" when it does not, and always for an upgrade, which
# rewrites the line, and for a project of its own.
def stale.at(up: Bool, +lock: String, +world: LW.World) -> String:
  match up:
    case True{}:
      ""
    case False{}:
      Mv.stale.world(lock, world)

# and at the root as the command found it
def stale(back: Back, +world: LW.World) -> String:
  match back:
    case Alone{}:
      ""
    case Back{_text, _spec, _fs, +lock}:
      stale.at(LW.args.upgrade(world), lock, world)

# the plan that refuses, writing nothing
def refused(+why: String) -> LP.Plan:
  LP.Plan{[], LP.Refused{why}}

# the files an upgrade rewrites, written ahead of the plan, unless it refuses
def edits.put(refuses: Bool, eds: List<&2, LP.Effect>, pl: LP.Plan) -> LP.Plan:
  match refuses:
    case True{}:
      pl
    case False{}:
      LP.Plan{es, outcome} = pl
      LP.Plan{List.append(&2, LP.Effect, eds, es), outcome}

# an upgrade's plan on the World it rewrote: the files it rewrote written
# first, so a source the lock planner rewrites too is left as the planner
# writes it, and then the planner's plan with the ledgers written back
def plan.up(got: Up, +back: Back) -> LP.Plan:
  Up{+w2, eds} = got
  edits.put(LP.refuses(w2), eds, plan.back(LP.plan(w2), writes(back, LP.ledger.next(w2))))

# a plain lock's plan, once it is known whether a line is stale
def plan.plain(fine: Bool, +why: String, +world: LW.World) -> LP.Plan:
  match fine:
    case True{}:
      LP.plan(world)
    case False{}:
      refused(why)

# what `ez lock` runs at a workspace root, under `--upgrade` or not
def plan.at(up: Bool, +back: Back, +world: LW.World) -> LP.Plan:
  match up:
    case True{}:
      match back:
        case Alone{}:
          LP.plan(world)
        case Back{+text, +spec, +fs, +lock}:
          plan.up(up.of(text, fs, lock, world), Back{text, spec, fs, lock})
    case False{}:
      match back:
        case Alone{}:
          LP.plan(world)
        case Back{_text, _spec, _fs, +lock}:
          +why = Mv.stale.world(lock, world)
          plan.plain(String.is_empty(why), why, world)

# what `ez lock` runs: for a project of its own, the plan the lock planner
# makes; at a workspace root, the plan it makes on the joint ledger, with,
# under `--upgrade`, every moved member's import lines rewritten and every
# ledger the upgrade changed written back in place of the joint one. A plain
# lock writes no ledger, so its plan is as it was, unless a line names a
# moved member's old hash, which it refuses.
def plan(back: Back, +world: LW.World) -> LP.Plan:
  match back:
    case Alone{}:
      LP.plan(world)
    case Back{+text, +spec, +fs, +lock}:
      plan.at(LW.args.upgrade(world), Back{text, spec, fs, lock}, world)

# the step a plain lock takes, once it is known whether a line is stale
def step.plain(fine: Bool, +why: String, +world: LW.World) -> LP.Step:
  match fine:
    case True{}:
      LP.step(world)
    case False{}:
      LP.Run{refused(why)}

# the lock planner's step on the World `ez lock` plans on: its questions, or
# its plan. A plain lock with a stale line asks nothing and refuses.
def step(+back: Back, +world: LW.World) -> LP.Step:
  +why = stale(back, world)
  step.plain(String.is_empty(why), why, plans.on(back, world))


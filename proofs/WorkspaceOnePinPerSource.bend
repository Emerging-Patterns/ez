# proofs of laws/WorkspaceOnePinPerSource.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/lock/world.bend as W
import ../src/ez/target.bend as Tgt
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../src/ws/up.bend as UUp
import ../src/ws/moved.bend as Mv
import ../src/ws/pin.bend as Pin
import ../laws/WorkspaceOnePinPerSource.bend as Laws
import ./lemmas/PlanEffectFacts.bend as M1

def Laws.combine_needs_pins(root, ms, ev):
  Eq.and.right(J.agree(J.all.deps(root, ms)), J.pins(J.all.deps(root, ms)), M1.join.deps(root, ms, ev))

# ---------------------------------------------------------------------------
# one pin per source

def Laws.up_alone(_world):
  {==}

# a workspace's plan under a plain lock is the planner's, when no line is
# stale
def up_plain_at(
  up: Bool,
  +text: String,
  +spec: WWorkspace.Spec,
  +fs: List<&2, J.Found>,
  +lock: String,
  +world: W.World,
  ev: {up == False{} : Bool},
  es: {UUp.stale.at(up, lock, world) == "" : String}
) -> {UUp.plan.at(up, UUp.Back{text, spec, fs, lock}, world) == P.plan(world) : P.Plan}:
  match up:
    case True{}:
      Eq.bit.absurd2(&2, {UUp.plan.at(True{}, UUp.Back{text, spec, fs, lock}, world) == P.plan(world) : P.Plan}, ev)
    case False{}:
      %Equal.sym(String, Mv.stale.world(lock, world), "", es)
        : {UUp.plan.plain(String.is_empty(_), _, world) == P.plan(world) : P.Plan}
      {==}

def Laws.up_plain(back, world, ev, es):
  match back:
    case UUp.Alone{}:
      {==}
    case UUp.Back{+text, +spec, +fs, +lock}:
      up_plain_at(W.args.upgrade(world), text, spec, fs, lock, world, ev, es)

def Laws.pin_back(nn, _hh, _ee, url, _rev, _tag, _root, _nar, vend, js, jn, jh, je, ju, jr, jt, jo, jnar, jv, ev):
  Equal.cong(M.Dep, M.Dep, dd => UUp.dep.back.at(M.Dep{nn, _hh, _ee, M.Git{url, _rev, _tag, _root, _nar, vend}}, dd),
    M.find(js, nn), M.Dep{jn, jh, je, M.Git{ju, jr, jt, jo, jnar, jv}}, ev)

def Laws.tool_pin_back(nn, ee, bb, url, _rev, _tag, _root, _nar, vend, ts, jn, je, jb, ju, jr, jt, jo, jnar, jv, ev):
  Equal.cong(M.Cli, M.Cli,
    dd => UUp.tool.back.at(M.Cli{nn, ee, bb, M.Git{url, _rev, _tag, _root, _nar, vend}}, dd),
    M.tool.find(ts, nn), M.Cli{jn, je, jb, M.Git{ju, jr, jt, jo, jnar, jv}}, ev)

def Laws.ref_unpinned(_nv, _url, _ref):
  {==}

def Laws.ref_takes_tag(_url, _ju, _rev, _ch, _tt, _jo, _jn, _jv):
  {==}

def Laws.ref_takes_rev(_url, _ju, _rev, _jo, _jn, _jv):
  {==}

# the tag compares equal to itself, so it is the pin
def Laws.ref_keeps_pin(url, _ju, rev, ch, tt, _jo, _jn, _jv):
  Equal.cong(Bool, Pin.Ref,
    bb => Bool.pick(Pin.Ref, bb, Pin.Given{SCon{ch, tt}},
      Pin.Held{"ez: the workspace pins " ++ url ++ " at " ++ Pin.held(rev, SCon{ch, tt}) ++
        "; move it for every member with ez lock --upgrade --package"}),
    Bool.or(String.eq(SCon{ch, tt}, SCon{ch, tt}), String.eq(SCon{ch, tt}, rev)), True{},
    Equal.cong(Bool, Bool, bb => Bool.or(bb, String.eq(SCon{ch, tt}, rev)),
      String.eq(SCon{ch, tt}, SCon{ch, tt}), True{}, Eq.string_eq_self(SCon{ch, tt})))

# neither the tag nor the commit, so the ref is held
def Laws.ref_holds_other(url, _ju, rev, tag, _jo, _jn, _jv, rc, rt, et, er):
  Equal.cong(Bool, Pin.Ref,
    bb => Bool.pick(Pin.Ref, bb, Pin.Given{SCon{rc, rt}},
      Pin.Held{"ez: the workspace pins " ++ url ++ " at " ++ Pin.held(rev, tag) ++
        "; move it for every member with ez lock --upgrade --package"}),
    Bool.or(String.eq(SCon{rc, rt}, tag), String.eq(SCon{rc, rt}, rev)), False{},
    Equal.trans(Bool, Bool.or(String.eq(SCon{rc, rt}, tag), String.eq(SCon{rc, rt}, rev)),
      Bool.or(False{}, String.eq(SCon{rc, rt}, rev)), False{},
      Equal.cong(Bool, Bool, bb => Bool.or(bb, String.eq(SCon{rc, rt}, rev)),
        String.eq(SCon{rc, rt}, tag), False{}, et), er))

def Laws.ref_named_free(pins, dir, home, target, ref, ev):
  Equal.cong(Bool, Pin.Ref,
    bb => Bool.pick(Pin.Ref, bb, Pin.Given{ref}, Pin.ref.place(Tgt.classify(target), pins, dir, home, ref)),
    Tgt.aim.named(Tgt.aim(target)), True{}, ev)

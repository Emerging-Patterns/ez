# proofs of laws/UpRefusalWritesNothing.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../src/ws/up.bend as UUp
import ../src/ws/moved.bend as Mv
import ../laws/RefusalWritesNothing.bend as L1
import ../laws/UpRefusalWritesNothing.bend as Laws
import ./lemmas/PlannerStages.bend as M1

# effects that write nothing write nothing once the ledgers' writes take the
# place of ez.toml's, since there was no write of ez.toml to replace
def back_writes_none(
  es: List<&2, P.Effect>,
  +ws: List<&2, P.Effect>,
  +ev: {P.writes.in(es) == False{} : Bool}
) -> {P.writes.in(UUp.effects.back(es, ws)) == False{} : Bool}:
  match es:
    case []:
      {==}
    case P.Write{at, text} <> tl:
      Eq.bit.absurd2(&2, {P.writes.in(UUp.effects.back(P.Write{at, text} <> tl, ws)) == False{} : Bool}, ev)
    case P.Lay{pl, hash, files} <> tl:
      Eq.bit.absurd2(&2, {P.writes.in(UUp.effects.back(P.Lay{pl, hash, files} <> tl, ws)) == False{} : Bool}, ev)
    case P.Drop{hash} <> tl:
      Eq.bit.absurd2(&2, {P.writes.in(UUp.effects.back(P.Drop{hash} <> tl, ws)) == False{} : Bool}, ev)
    case P.Say{_text} <> +tl:
      back_writes_none(tl, ws, ev)
    case P.Name{nv, hash} <> tl:
      Eq.bit.absurd2(&2, {P.writes.in(UUp.effects.back(P.Name{nv, hash} <> tl, ws)) == False{} : Bool}, ev)

# and so for a plan
def back_plan_writes_none(
  pl: P.Plan,
  +ws: List<&2, P.Effect>,
  +ev: {P.writes(pl) == False{} : Bool}
) -> {P.writes(UUp.plan.back(pl, ws)) == False{} : Bool}:
  match pl:
    case P.Plan{es, _outcome}:
      back_writes_none(es, ws, ev)

# a plain lock's plan on a World that refuses writes nothing, whether a
# line is stale or not
def plain_refused(
  fine: Bool,
  +why: String,
  +world: W.World,
  +er: {P.refuses(world) == True{} : Bool}
) -> {P.writes(UUp.plan.plain(fine, why, world)) == False{} : Bool}:
  match fine:
    case True{}:
      L1.lock_refusal_writes_nothing(world, er)
    case False{}:
      {==}

# a workspace's plan that refuses writes nothing, upgrade or not
def up_refused_at(
  up: Bool,
  +text: String,
  +spec: WWorkspace.Spec,
  +fs: List<&2, J.Found>,
  +lock: String,
  +world: W.World,
  +er: {P.refuses(UUp.world.at(up, text, fs, lock, world)) == True{} : Bool}
) -> {P.writes(UUp.plan.at(up, UUp.Back{text, spec, fs, lock}, world)) == False{} : Bool}:
  match up:
    case True{}:
      +w2 = UUp.up.world(UUp.up.of(text, fs, lock, world))
      %Equal.sym(Bool, P.refuses(w2), True{}, er)
        : {P.writes(UUp.edits.put(_, Mv.edits(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, UUp.files.of(world), lock,
            W.args.only(world)))), UUp.files.of(world)),
          UUp.plan.back(P.plan(w2), UUp.writes(UUp.Back{text, spec, fs, lock}, P.ledger.next(w2)))))
          == False{} : Bool}
      back_plan_writes_none(P.plan(w2), UUp.writes(UUp.Back{text, spec, fs, lock}, P.ledger.next(w2)),
        L1.lock_refusal_writes_nothing(w2, er))
    case False{}:
      plain_refused(String.is_empty(Mv.stale.world(lock, world)), Mv.stale.world(lock, world), world, er)

def Laws.up_refusal_writes_nothing(back, world, er):
  match back:
    case UUp.Alone{}:
      L1.lock_refusal_writes_nothing(world, er)
    case UUp.Back{+text, +spec, +fs, +lock}:
      up_refused_at(W.args.upgrade(world), text, spec, fs, lock, world, er)

# proofs of laws/WorkspaceUpgradeWritesJointLock.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/pkg/pkg.bend as K
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/ledger/upgrade.bend as U
import ../src/lock/world.bend as W
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../src/ws/up.bend as UUp
import ../src/ws/moved.bend as Mv
import ../laws/WorkspaceUpgradeWritesJointLock.bend as Laws
import ./lemmas/PlannerStages.bend as M1

# whether no effect of a list writes at a path
def misses(es: List<&2, P.Effect>, +path: String) -> Bool:
  match es:
    case []:
      True{}
    case P.Write{at, _text} <> tl:
      Bool.and(Bool.not(String.eq(at, path)), misses(tl, path))
    case _hd <> tl:
      misses(tl, path)

# a write elsewhere leaves what the effects after it leave at a path
def put_one_miss(
  +at: String,
  text: String,
  +path: String,
  rest: P.Wrote,
  ev: {String.eq(at, path) == False{} : Bool}
) -> {P.put.one(P.Write{at, text}, path, rest) == rest : P.Wrote}:
  match rest:
    case P.Kept{}:
      Equal.cong(Bool, P.Wrote, bb => Bool.pick(P.Wrote, bb, P.Put{text}, P.Kept{}),
        String.eq(at, path), False{}, ev)
    case P.Put{_later}:
      {==}

# writes that miss a path, put in front, leave it as what follows leaves it
def app_misses(
  ws: List<&2, P.Effect>,
  +rest: List<&2, P.Effect>,
  +path: String,
  +ev: {misses(ws, path) == True{} : Bool}
) -> {P.put.in(List.append(&2, P.Effect, ws, rest), path) == P.put.in(rest, path) : P.Wrote}:
  match ws:
    case []:
      {==}
    case P.Write{+at, +text} <> +tl:
      Equal.trans(P.Wrote,
        P.put.one(P.Write{at, text}, path, P.put.in(List.append(&2, P.Effect, tl, rest), path)),
        P.put.in(List.append(&2, P.Effect, tl, rest), path),
        P.put.in(rest, path),
        put_one_miss(at, text, path, P.put.in(List.append(&2, P.Effect, tl, rest), path),
          Eq.not.true(String.eq(at, path),
            Eq.and.left(Bool.not(String.eq(at, path)), misses(tl, path), ev))),
        app_misses(tl, rest, path, Eq.and.right(Bool.not(String.eq(at, path)), misses(tl, path), ev)))
    case P.Lay{_pl, _hash, _files} <> +tl:
      app_misses(tl, rest, path, ev)
    case P.Drop{_hash} <> +tl:
      app_misses(tl, rest, path, ev)
    case P.Say{_text} <> +tl:
      app_misses(tl, rest, path, ev)
    case P.Name{_nv, _hash} <> +tl:
      app_misses(tl, rest, path, ev)

# a write kept, or the ledgers' in place of ez.toml's, leaves the lock as the
# plan left it
def write_back_lock(
  hit: Bool,
  +at: String,
  +text: String,
  +ws: List<&2, P.Effect>,
  +tl: List<&2, P.Effect>,
  eh: {String.eq(at, "ez.toml") == hit : Bool},
  +ev: {misses(ws, P.lockfile()) == True{} : Bool},
  ih: {P.put.in(UUp.effects.back(tl, ws), P.lockfile()) == P.put.in(tl, P.lockfile()) : P.Wrote}
) -> {P.put.in(UUp.effect.write(hit, at, text, ws, UUp.effects.back(tl, ws)), P.lockfile())
    == P.put.one(P.Write{at, text}, P.lockfile(), P.put.in(tl, P.lockfile())) : P.Wrote}:
  match hit:
    case True{}:
      Equal.trans(P.Wrote,
        P.put.in(List.append(&2, P.Effect, ws, UUp.effects.back(tl, ws)), P.lockfile()),
        P.put.in(tl, P.lockfile()),
        P.put.one(P.Write{at, text}, P.lockfile(), P.put.in(tl, P.lockfile())),
        Equal.trans(P.Wrote,
          P.put.in(List.append(&2, P.Effect, ws, UUp.effects.back(tl, ws)), P.lockfile()),
          P.put.in(UUp.effects.back(tl, ws), P.lockfile()),
          P.put.in(tl, P.lockfile()),
          app_misses(ws, UUp.effects.back(tl, ws), P.lockfile(), ev), ih),
        Equal.sym(P.Wrote,
          P.put.one(P.Write{at, text}, P.lockfile(), P.put.in(tl, P.lockfile())),
          P.put.in(tl, P.lockfile()),
          put_one_miss(at, text, P.lockfile(), P.put.in(tl, P.lockfile()),
            Equal.cong(String, Bool, ss => String.eq(ss, P.lockfile()), at, "ez.toml",
              Str.string_eq_true(at, "ez.toml", eh)))))
    case False{}:
      Equal.cong(P.Wrote, P.Wrote, rr => P.put.one(P.Write{at, text}, P.lockfile(), rr),
        P.put.in(UUp.effects.back(tl, ws), P.lockfile()), P.put.in(tl, P.lockfile()), ih)

# by induction on the effects: each is kept, or is the write of ez.toml,
# which the ledgers' writes replace and none of which is the lock's
def effects_back_lock(
  es: List<&2, P.Effect>,
  +ws: List<&2, P.Effect>,
  +ev: {misses(ws, P.lockfile()) == True{} : Bool}
) -> {P.put.in(UUp.effects.back(es, ws), P.lockfile()) == P.put.in(es, P.lockfile()) : P.Wrote}:
  match es:
    case []:
      {==}
    case P.Write{+at, +text} <> +tl:
      write_back_lock(String.eq(at, "ez.toml"), at, text, ws, tl, {==}, ev, effects_back_lock(tl, ws, ev))
    case P.Lay{_pl, _hash, _files} <> +tl:
      effects_back_lock(tl, ws, ev)
    case P.Drop{_hash} <> +tl:
      effects_back_lock(tl, ws, ev)
    case P.Say{_text} <> +tl:
      effects_back_lock(tl, ws, ev)
    case P.Name{_nv, _hash} <> +tl:
      effects_back_lock(tl, ws, ev)

# the two halves of a list of writes miss a path when each does
def misses_app(
  as: List<&2, P.Effect>,
  +bs: List<&2, P.Effect>,
  +path: String,
  +ea: {misses(as, path) == True{} : Bool},
  eb: {misses(bs, path) == True{} : Bool}
) -> {misses(List.append(&2, P.Effect, as, bs), path) == True{} : Bool}:
  match as:
    case []:
      eb
    case P.Write{+at, _text} <> +tl:
      Str.and_true(Bool.not(String.eq(at, path)), misses(List.append(&2, P.Effect, tl, bs), path),
        Eq.and.left(Bool.not(String.eq(at, path)), misses(tl, path), ea),
        misses_app(tl, bs, path, Eq.and.right(Bool.not(String.eq(at, path)), misses(tl, path), ea), eb))
    case P.Lay{_pl, _hash, _files} <> +tl:
      misses_app(tl, bs, path, ea, eb)
    case P.Drop{_hash} <> +tl:
      misses_app(tl, bs, path, ea, eb)
    case P.Say{_text} <> +tl:
      misses_app(tl, bs, path, ea, eb)
    case P.Name{_nv, _hash} <> +tl:
      misses_app(tl, bs, path, ea, eb)

# a ledger written back, or not, misses the lock when its path is not the
# lock's
def pick_miss(
  bb: Bool,
  +at: String,
  text: String,
  ev: {String.eq(at, P.lockfile()) == False{} : Bool}
) -> {misses(Bool.pick(List<&2, P.Effect>, bb, [], [P.Write{at, text}]), P.lockfile()) == True{} : Bool}:
  match bb:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Bool, Bool, xx => Bool.and(Bool.not(xx), True{}), String.eq(at, P.lockfile()), False{}, ev)

# a member's ledger is not the lock: its path holds a `/`
def member_not_lock(
  hit: Bool,
  +pre: String,
  eh: {String.eq(pre ++ "/ez.toml", P.lockfile()) == hit : Bool}
) -> {String.eq(pre ++ "/ez.toml", P.lockfile()) == False{} : Bool}:
  match hit:
    case False{}:
      eh
    case True{}:
      Eq.bit.absurd2(&2, {String.eq(pre ++ "/ez.toml", P.lockfile()) == False{} : Bool},
        Equal.trans(Bool, True{}, Str.clear(pre ++ "/ez.toml", '/'), False{},
          Equal.sym(Bool, Str.clear(pre ++ "/ez.toml", '/'), True{},
            Equal.cong(String, Bool, ss => Str.clear(ss, '/'), pre ++ "/ez.toml", P.lockfile(),
              Str.string_eq_true(pre ++ "/ez.toml", P.lockfile(), eh))),
          M1.slash_member(pre)))

# a member's ledger written back misses the lock
def member_write_miss(
  rd: M.Read,
  +ds: List<&2, String>,
  +joint: M.Manifest
) -> {misses(UUp.member.write(rd, ds, joint), P.lockfile()) == True{} : Bool}:
  match rd:
    case M.Bad{_why}:
      {==}
    case M.Good{+mm}:
      pick_miss(String.eq(Rend.show(mm), Rend.show(UUp.ledger.back(mm, joint))),
        WWorkspace.segs.text(ds) ++ "/ez.toml", Rend.show(UUp.ledger.back(mm, joint)),
        member_not_lock(String.eq(WWorkspace.segs.text(ds) ++ "/ez.toml", P.lockfile()), WWorkspace.segs.text(ds),
            {==}))

# a member's, kept or passed by
def found_pick_miss(
  bb: Bool,
  +text: String,
  +ds: List<&2, String>,
  +joint: M.Manifest
) -> {misses(UUp.found.pick(bb, text, ds, joint), P.lockfile()) == True{} : Bool}:
  match bb:
    case True{}:
      member_write_miss(M.parse(text), ds, joint)
    case False{}:
      {==}

# one ez.toml git listed, written back or not, misses the lock
def found_write_miss(
  lg: Maybe<&2, WWorkspace.Ledger>,
  +text: String,
  +dirs: List<&2, List<&2, String>>,
  +joint: M.Manifest
) -> {misses(UUp.found.write(lg, text, dirs, joint), P.lockfile()) == True{} : Bool}:
  match lg:
    case None{}:
      {==}
    case Some{WWorkspace.Ledger{+ds, nn, ww}}:
      found_pick_miss(WWorkspace.has(dirs, ds), text, ds, joint)

# every member's ledger written back misses the lock
def members_write_miss(
  fs: List<&2, J.Found>,
  +dirs: List<&2, List<&2, String>>,
  +joint: M.Manifest
) -> {misses(UUp.members.write(fs, dirs, joint), P.lockfile()) == True{} : Bool}:
  match fs:
    case []:
      {==}
    case J.Found{+pp, +tt} <> +tl:
      misses_app(UUp.found.write(WWorkspace.ledger.of(pp, tt), tt, dirs, joint), UUp.members.write(tl, dirs, joint),
        P.lockfile(), found_write_miss(WWorkspace.ledger.of(pp, tt), tt, dirs, joint),
        members_write_miss(tl, dirs, joint))

# the root's ledger written back misses the lock: it is ez.toml
def root_write_miss(
  rd: M.Read,
  +spec: WWorkspace.Spec,
  +root: WWorkspace.Root,
  +joint: M.Manifest
) -> {misses(UUp.root.write(rd, spec, root, joint), P.lockfile()) == True{} : Bool}:
  match rd:
    case M.Bad{_why}:
      {==}
    case M.Good{+mm}:
      pick_miss(String.eq(Rend.show(mm), Rend.show(UUp.ledger.back(mm, joint))), "ez.toml",
        UUp.root.text(UUp.ledger.back(mm, joint), spec, root), {==})

# every ledger written back misses the lock, once the member set is known
def members_miss(
  ms: WWorkspace.Members,
  +text: String,
  +spec: WWorkspace.Spec,
  +fs: List<&2, J.Found>,
  +joint: M.Manifest
) -> {misses(UUp.writes.members(ms, text, spec, fs, joint), P.lockfile()) == True{} : Bool}:
  match ms:
    case WWorkspace.Refused{_why}:
      {==}
    case WWorkspace.Members{_root, +dirs}:
      misses_app(UUp.root.write(M.parse(text), spec, WWorkspace.root.of(text), joint), UUp.members.write(fs, dirs,
          joint),
        P.lockfile(), root_write_miss(M.parse(text), spec, WWorkspace.root.of(text), joint),
        members_write_miss(fs, dirs, joint))

# and once the joint ledger was read
def joint_miss(
  joint: M.Read,
  +text: String,
  +spec: WWorkspace.Spec,
  +fs: List<&2, J.Found>
) -> {misses(UUp.writes.joint(joint, text, spec, fs), P.lockfile()) == True{} : Bool}:
  match joint:
    case M.Bad{_why}:
      {==}
    case M.Good{+jm}:
      members_miss(WWorkspace.members(spec, WWorkspace.root.of(text), J.ledgers(fs)), text, spec, fs, jm)

# a plan with the ledgers' writes in place of ez.toml's leaves the lock as it
# was
def up_lock_plan(
  pl: P.Plan,
  +ws: List<&2, P.Effect>,
  +ev: {misses(ws, P.lockfile()) == True{} : Bool}
) -> {P.put.plan(UUp.plan.back(pl, ws), P.lockfile()) == P.put.plan(pl, P.lockfile()) : P.Wrote}:
  match pl:
    case P.Plan{es, _outcome}:
      effects_back_lock(es, ws, ev)

# effects that write nothing at a path, ahead of others, leave what the
# others leave there
def put_skip(
  eds: List<&2, P.Effect>,
  +es: List<&2, P.Effect>,
  +path: String,
  +em: {misses(eds, path) == True{} : Bool}
) -> {P.put.in(List.append(&2, P.Effect, eds, es), path) == P.put.in(es, path) : P.Wrote}:
  match eds:
    case []:
      {==}
    case P.Write{+at, +text} <> +tl:
      +rest = put_skip(tl, es, path, Eq.and.right(Bool.not(String.eq(at, path)), misses(tl, path), em))
      Equal.trans(P.Wrote,
        P.put.one(P.Write{at, text}, path, P.put.in(List.append(&2, P.Effect, tl, es), path)),
        P.put.one(P.Write{at, text}, path, P.put.in(es, path)),
        P.put.in(es, path),
        Equal.cong(P.Wrote, P.Wrote, w => P.put.one(P.Write{at, text}, path, w),
          P.put.in(List.append(&2, P.Effect, tl, es), path), P.put.in(es, path), rest),
        put_one_miss(at, text, path, P.put.in(es, path),
          Eq.not.true(String.eq(at, path), Eq.and.left(Bool.not(String.eq(at, path)), misses(tl, path), em))))
    case P.Lay{_pl, _hash, _files} <> +tl:
      put_skip(tl, es, path, em)
    case P.Drop{_hash} <> +tl:
      put_skip(tl, es, path, em)
    case P.Say{_text} <> +tl:
      put_skip(tl, es, path, em)
    case P.Name{_nv, _hash} <> +tl:
      put_skip(tl, es, path, em)

# a rewritten file's write, once it is known whether it would land on the lock
def edit_pick_miss(
  hit: Bool,
  +at: String,
  +text: String,
  +rest: List<&2, P.Effect>,
  eh: {String.eq(at, P.lockfile()) == hit : Bool},
  +er: {misses(rest, P.lockfile()) == True{} : Bool}
) -> {misses(Bool.pick(List<&2, P.Effect>, hit, rest, P.Write{at, text} <> rest), P.lockfile()) == True{} : Bool}:
  match hit:
    case True{}:
      er
    case False{}:
      %Equal.sym(Bool, String.eq(at, P.lockfile()), False{}, eh)
        : {Bool.and(Bool.not(_), misses(rest, P.lockfile())) == True{} : Bool}
      er

# a rewritten file's write misses the lock, changed or not
def edit_miss(
  changed: Bool,
  +at: String,
  +text: String,
  +rest: List<&2, P.Effect>,
  +er: {misses(rest, P.lockfile()) == True{} : Bool}
) -> {misses(Mv.edit.put(changed, at, text, rest), P.lockfile()) == True{} : Bool}:
  match changed:
    case True{}:
      edit_pick_miss(String.eq(at, P.lockfile()), at, text, rest, {==}, er)
    case False{}:
      er

# the files the moves rewrite never write the lock
def edits_miss(
  +ss: List<&2, U.Swap>,
  fs: List<&2, K.Source>
) -> {misses(Mv.edits(ss, fs), P.lockfile()) == True{} : Bool}:
  match fs:
    case []:
      {==}
    case K.Source{+at, +text} <> +tl:
      edit_miss(Bool.not(String.eq(U.reimport.many(ss, text), text)), at, U.reimport.many(ss, text),
        Mv.edits(ss, tl), edits_miss(ss, tl))

# the files an upgrade rewrites, put ahead of a plan, leave its lock as it was
def edits_put_lock(
  refuses: Bool,
  +eds: List<&2, P.Effect>,
  pl: P.Plan,
  +em: {misses(eds, P.lockfile()) == True{} : Bool}
) -> {P.put.plan(UUp.edits.put(refuses, eds, pl), P.lockfile()) == P.put.plan(pl, P.lockfile()) : P.Wrote}:
  match refuses:
    case True{}:
      {==}
    case False{}:
      match pl:
        case P.Plan{+es, _outcome}:
          put_skip(eds, es, P.lockfile(), em)

# a workspace's plan writes the lock its planner does on the World it plans
# on, upgrade or not
def up_lock_at(
  up: Bool,
  +text: String,
  +spec: WWorkspace.Spec,
  +fs: List<&2, J.Found>,
  +lock: String,
  +world: W.World,
  es: {UUp.stale.at(up, lock, world) == "" : String}
) -> {P.put.plan(UUp.plan.at(up, UUp.Back{text, spec, fs, lock}, world), P.lockfile())
    == P.put(UUp.world.at(up, text, fs, lock, world), P.lockfile()) : P.Wrote}:
  match up:
    case True{}:
      +w2 = UUp.up.world(UUp.up.of(text, fs, lock, world))
      +ss = Mv.swaps(Mv.cascade(Mv.ctx(text, fs, UUp.files.of(world), lock, W.args.only(world))))
      +pb = UUp.plan.back(P.plan(w2), UUp.writes(UUp.Back{text, spec, fs, lock}, P.ledger.next(w2)))
      Equal.trans(P.Wrote,
        P.put.plan(UUp.edits.put(P.refuses(w2), Mv.edits(ss, UUp.files.of(world)), pb), P.lockfile()),
        P.put.plan(pb, P.lockfile()),
        P.put(w2, P.lockfile()),
        edits_put_lock(P.refuses(w2), Mv.edits(ss, UUp.files.of(world)), pb, edits_miss(ss, UUp.files.of(world))),
        up_lock_plan(P.plan(w2), UUp.writes(UUp.Back{text, spec, fs, lock}, P.ledger.next(w2)),
          joint_miss(P.ledger.next(w2), text, spec, fs)))
    case False{}:
      %Equal.sym(String, Mv.stale.world(lock, world), "", es)
        : {P.put.plan(UUp.plan.plain(String.is_empty(_), _, world), P.lockfile())
          == P.put(world, P.lockfile()) : P.Wrote}
      {==}

def Laws.up_writes_the_lock(back, world, es):
  match back:
    case UUp.Alone{}:
      {==}
    case UUp.Back{+text, +spec, +fs, +lock}:
      up_lock_at(W.args.upgrade(world), text, spec, fs, lock, world, es)

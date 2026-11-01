# proofs of laws/WorkspaceAddRemoveRelock.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/relock/relock.bend as R
import ../src/lock/plan.bend as P
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/lock/world.bend as W
import ../src/add/relock.bend as AR
import ../src/remove/relock.bend as RR
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../src/ws/up.bend as UUp
import ../src/ws/relock.bend as Rel
import ../laws/WorkspaceAddRemoveRelock.bend as Laws
import ./lemmas/AddPlanEffects.bend as M1

# ---------------------------------------------------------------------------
# `ez add` and `ez remove` in a workspace

def Laws.at_write(_at, _path, _text):
  {==}

def Laws.at_committed(_at, _hash, _fs):
  {==}

def Laws.at_cache(_at, _hash, _fs):
  {==}

def Laws.at_drop(_at, _hash):
  {==}

def Laws.at_say(_at, _text):
  {==}

def Laws.at_name(_at, _nv, _hash):
  {==}

def Laws.at_plan_effects(_at, pl):
  match pl:
    case P.Plan{_es, _o}:
      {==}

def Laws.at_plan_refuses(_at, pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

def Laws.keep_root(old, text, spec, mm, ws, rd):
  %Equal.sym(WWorkspace.Read, WWorkspace.spec.of(old), WWorkspace.Root{spec}, ws)
    : {Rel.keep.read(_, old, text) == UUp.root.text(mm, spec, WWorkspace.root.of(old)) : String}
  %Equal.sym(M.Read, M.parse(text), M.Good{mm}, rd)
    : {Rel.keep.parsed(_, spec, WWorkspace.root.of(old), text) == UUp.root.text(mm, spec,
        WWorkspace.root.of(old)) : String}
  {==}

def Laws.keep_lone(old, text, ws):
  %Equal.sym(WWorkspace.Read, WWorkspace.spec.of(old), WWorkspace.Lone{}, ws) : {Rel.keep.read(_, old,
      text) == text : String}
  {==}

def Laws.keep_ledger_write(_old, _text):
  {==}

def Laws.keep_other_write(old, path, text, other):
  %Equal.sym(Bool, String.eq(path, "ez.toml"), False{}, other)
    : {Rel.keep.write(_, old, path, text) == P.Write{path, text} : P.Effect}
  {==}

def Laws.edit_root(_old, _es, _outcome):
  {==}

def Laws.edit_member(_hd, _tl, _old, _pl):
  {==}

def Laws.ledgers_root(_new, _text, _fs):
  {==}

def Laws.ledgers_member(_hd, _tl, _new, _text, _fs):
  {==}

def Laws.put_found_hit(path, was, tl, text):
  %Equal.sym(Bool, String.eq(path, path), True{}, Eq.string_eq_self(path))
    : {Rel.put.pick(_, path, was, text, Rel.put.found(tl, path, text))
      == J.Found{path, text} <> Rel.put.found(tl, path, text) : List<&2, J.Found>}
  {==}

def Laws.put_found_miss(fp, was, tl, path, text, other):
  %Equal.sym(Bool, String.eq(fp, path), False{}, other)
    : {Rel.put.pick(_, fp, was, text, Rel.put.found(tl, path, text))
      == J.Found{fp, was} <> Rel.put.found(tl, path, text) : List<&2, J.Found>}
  {==}

def Laws.ledgers_write(_at, rel, text, fs, _listing, _lock, pl, was, new, put):
  %Equal.sym(P.Wrote, P.put.plan(pl, "ez.toml"), P.Put{new}, put)
    : {Rel.ledgers.at(rel, Rel.new.of(R.ledger.of(_, was)), text, fs) == Rel.ledgers.at(rel, new, text, fs)
      : Rel.Ledgers}
  {==}

def Laws.lock_root_plain(at, _rel, _was, _found, listing, lock, text, fs, rs, spec, mm, ws, jj):
  %Equal.sym(WWorkspace.Read, WWorkspace.spec.of(text), WWorkspace.Root{spec}, ws)
    : {Rel.lock.plan(Rel.lock.read(_, at, text, fs, listing, lock, rs))
      == UUp.plan(UUp.Back{text, spec, fs, lock}, W.World{W.Args{False{}, "", at}, Some{Rend.show(mm)}, listing,
      List.append(&2, W.Reply, J.seeds(J.Joint{mm}, J.files(listing)), rs), []}) : P.Plan}
  %Equal.sym(J.Joint, J.joint(text, fs, J.files(listing)), J.Joint{mm}, jj)
    : {Rel.lock.plan(Rel.lock.joint(_, at, text, spec, fs, listing, lock, rs))
      == UUp.plan(UUp.Back{text, spec, fs, lock}, W.World{W.Args{False{}, "", at}, Some{Rend.show(mm)}, listing,
      List.append(&2, W.Reply, J.seeds(J.Joint{mm}, J.files(listing)), rs), []}) : P.Plan}
  {==}

def Laws.lock_root_clash(at, _rel, _was, _found, listing, lock, text, fs, rs, spec, why, ws, jj):
  %Equal.sym(WWorkspace.Read, WWorkspace.spec.of(text), WWorkspace.Root{spec}, ws)
    : {Rel.lock.plan(Rel.lock.read(_, at, text, fs, listing, lock, rs)) == P.Plan{[], P.Refused{why}} : P.Plan}
  %Equal.sym(J.Joint, J.joint(text, fs, J.files(listing)), J.Clash{why}, jj)
    : {Rel.lock.plan(Rel.lock.joint(_, at, text, spec, fs, listing, lock, rs)) == P.Plan{[], P.Refused{why}}
      : P.Plan}
  {==}

def Laws.lock_root_bad(at, _rel, _was, _found, listing, lock, text, fs, rs, why, ws):
  %Equal.sym(WWorkspace.Read, WWorkspace.spec.of(text), WWorkspace.Bad{why}, ws)
    : {Rel.lock.plan(Rel.lock.read(_, at, text, fs, listing, lock, rs)) == P.Plan{[], P.Refused{why}} : P.Plan}
  {==}

def Laws.add_ws_locks_what_it_writes(_root, _aw, _listing, _locks):
  {==}

def Laws.add_ws_runs_add_then_lock(root, w, ok):
  match w:
    case AR.World{+a, +listing, +locks}:
      M1.join_effects(Rel.add.edit(root, a),
        Rel.at.plan(Rel.rooted.at(root), Rel.lock.plan(Rel.add.lock(root, AR.World{a, listing, locks}))),
        Rel.add.notes(Rel.add.lock(root, AR.World{a, listing, locks}), a), AR.tail(a), ok)

# LAW: the root's lock plan, from the root, refuses when the plan does
law at_plan_refused:
  for +at: String
  for pl: P.Plan
  for r: {R.refuses(pl) == True{} : Bool}
  {R.refuses(Rel.at.plan(at, pl)) == True{} : Bool}

def at_plan_refused(at, pl, r):
  match pl:
    case P.Plan{es, o}:
      match o:
        case P.Success{}:
          Eq.bit.absurd(&2, {R.refuses(Rel.at.plan(at, P.Plan{es, P.Success{}})) == True{} : Bool}, r)
        case P.Refused{_why}:
          {==}

def Laws.add_ws_refuses_with_lock(root, w, r):
  match w:
    case AR.World{+a, +listing, +locks}:
      +lk = Rel.lock.plan(Rel.add.lock(root, AR.World{a, listing, locks}))
      M1.join_refuses_lock(Rel.add.edit(root, a), Rel.at.plan(Rel.rooted.at(root), lk),
        Rel.add.notes(Rel.add.lock(root, AR.World{a, listing, locks}), a), AR.tail(a),
        at_plan_refused(Rel.rooted.at(root), lk, r))

def Laws.add_ws_notes(_back, _world, _aw):
  {==}

def Laws.add_own(_w):
  {==}

def Laws.add_own_next(_w):
  {==}

def Laws.add_inside(_root, _w):
  {==}

def Laws.remove_ws_locks_what_it_writes(_root, _rw, _here, _listing, _locks):
  {==}

def Laws.remove_ws_runs_remove_then_lock(root, w, ok):
  match w:
    case RR.World{+r, +here, +listing, +locks}:
      M1.join_effects(Rel.remove.edit(root, r),
        Rel.at.plan(Rel.rooted.at(root), Rel.lock.plan(Rel.remove.lock(root, RR.World{r, here, listing, locks}))),
        [], RR.tail(), ok)

def Laws.remove_ws_refuses_with_lock(root, w, rf):
  match w:
    case RR.World{+r, +here, +listing, +locks}:
      +lk = Rel.lock.plan(Rel.remove.lock(root, RR.World{r, here, listing, locks}))
      M1.join_refuses_lock(Rel.remove.edit(root, r), Rel.at.plan(Rel.rooted.at(root), lk), [], RR.tail(),
        at_plan_refused(Rel.rooted.at(root), lk, rf))

def Laws.remove_own(_w):
  {==}

def Laws.remove_own_next(_w):
  {==}

def Laws.remove_inside(_root, _w):
  {==}

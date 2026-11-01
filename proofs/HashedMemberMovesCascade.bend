# proofs of laws/HashedMemberMovesCascade.bend
import Base
import ../src/check/str.bend as Str
import ../src/lock/plan.bend as P
import ../src/ledger/upgrade.bend as U
import ../src/lock/world.bend as W
import ../src/ws/joint.bend as J
import ../src/ws/up.bend as UUp
import ../src/ws/moved.bend as Mv
import ../laws/HashedMemberMovesCascade.bend as Laws

# ---------------------------------------------------------------------------
# a member imported by its hash, once it moved

def Laws.stale_plain_refuses(text, spec, fs, lock, world, why, ev, ew, en):
  %Equal.sym(Bool, W.args.upgrade(world), False{}, ev)
    : {UUp.plan.at(_, UUp.Back{text, spec, fs, lock}, world) == P.Plan{[], P.Refused{why}} : P.Plan}
  %Equal.sym(String, Mv.stale.world(lock, world), why, ew)
    : {UUp.plan.plain(String.is_empty(_), _, world) == P.Plan{[], P.Refused{why}} : P.Plan}
  %Equal.sym(Bool, String.is_empty(why), False{}, en)
    : {UUp.plan.plain(_, why, world) == P.Plan{[], P.Refused{why}} : P.Plan}
  {==}

def Laws.stale_plain_asks_nothing(text, spec, fs, lock, world, why, ev, ew, en):
  %Equal.sym(Bool, W.args.upgrade(world), False{}, ev)
    : {UUp.step.plain(String.is_empty(UUp.stale.at(_, lock, world)), UUp.stale.at(_, lock, world),
        UUp.plans.on(UUp.Back{text, spec, fs, lock}, world))
      == P.Run{P.Plan{[], P.Refused{why}}} : P.Step}
  %Equal.sym(String, Mv.stale.world(lock, world), why, ew)
    : {UUp.step.plain(String.is_empty(_), _, UUp.plans.on(UUp.Back{text, spec, fs, lock}, world))
      == P.Run{P.Plan{[], P.Refused{why}}} : P.Step}
  %Equal.sym(Bool, String.is_empty(why), False{}, en)
    : {UUp.step.plain(_, why, UUp.plans.on(UUp.Back{text, spec, fs, lock}, world))
      == P.Run{P.Plan{[], P.Refused{why}}} : P.Step}
  {==}

def Laws.stale_names_upgrade(name, old, new, rest, at, text, eh):
  %Equal.sym(Bool, String.eq(U.reimport.many([U.Swap{old, new}], text), text), False{}, eh)
    : {Bool.pick(String, _, Mv.stale.moves(rest, at, text),
        "ez: " ++ at ++ " imports workspace member " ++ name ++ " by " ++ old ++
          ", the hash the lock records for it, and the member is " ++ new ++
          " now; ez lock --upgrade --package " ++ name ++ " rewrites the import")
      == "ez: " ++ at ++ " imports workspace member " ++ name ++ " by " ++ old ++
        ", the hash the lock records for it, and the member is " ++ new ++
        " now; ez lock --upgrade --package " ++ name ++ " rewrites the import" : String}
  {==}

def Laws.stale_skips_move(name, old, new, rest, at, text, eh):
  %Equal.sym(Bool, String.eq(U.reimport.many([U.Swap{old, new}], text), text), True{}, eh)
    : {Bool.pick(String, _, Mv.stale.moves(rest, at, text),
        "ez: " ++ at ++ " imports workspace member " ++ name ++ " by " ++ old ++
          ", the hash the lock records for it, and the member is " ++ new ++
          " now; ez lock --upgrade --package " ++ name ++ " rewrites the import")
      == Mv.stale.moves(rest, at, text) : String}
  {==}

def Laws.stale_first_file(ms, at, text, tl, why, eh, en):
  %Equal.sym(String, Mv.stale.moves(ms, at, text), why, eh)
    : {Bool.pick(String, String.is_empty(_), Mv.stale(ms, tl), _) == why : String}
  %Equal.sym(Bool, String.is_empty(why), False{}, en)
    : {Bool.pick(String, _, Mv.stale(ms, tl), why) == why : String}
  {==}

def Laws.stale_skips_file(ms, at, text, tl, eh):
  %Equal.sym(String, Mv.stale.moves(ms, at, text), "", eh)
    : {Bool.pick(String, String.is_empty(_), Mv.stale(ms, tl), _) == Mv.stale(ms, tl) : String}
  {==}

def Laws.move_chosen(_path, name, new, base, old, only, rest, eo, ec):
  %Equal.sym(Bool, String.eq(new, old), False{}, eo)
    : {Mv.move.put(Bool.and(Bool.not(_), Bool.or(U.chosen(only, name), Bool.not(String.eq(new, base)))),
        name, old, new, rest) == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  %Equal.sym(Bool, U.chosen(only, name), True{}, ec)
    : {Mv.move.put(Bool.or(_, Bool.not(String.eq(new, base))), name, old, new, rest)
      == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  {==}

def Laws.move_rewritten(_path, name, new, base, old, only, rest, eo, ec, eb):
  %Equal.sym(Bool, String.eq(new, old), False{}, eo)
    : {Mv.move.put(Bool.and(Bool.not(_), Bool.or(U.chosen(only, name), Bool.not(String.eq(new, base)))),
        name, old, new, rest) == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  %Equal.sym(Bool, U.chosen(only, name), False{}, ec)
    : {Mv.move.put(Bool.or(_, Bool.not(String.eq(new, base))), name, old, new, rest)
      == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  %Equal.sym(Bool, String.eq(new, base), False{}, eb)
    : {Mv.move.put(Bool.not(_), name, old, new, rest) == Mv.Shift{name, old, new} <> rest : List<&2, Mv.Shift>}
  {==}

def Laws.move_same(_path, name, new, base, old, only, rest, eo):
  %Equal.sym(Bool, String.eq(new, old), True{}, eo)
    : {Mv.move.put(Bool.and(Bool.not(_), Bool.or(U.chosen(only, name), Bool.not(String.eq(new, base)))),
        name, old, new, rest) == rest : List<&2, Mv.Shift>}
  {==}

def Laws.move_untouched(_path, name, new, base, old, only, rest, ec, eb):
  %Equal.sym(Bool, U.chosen(only, name), False{}, ec)
    : {Mv.move.put(Bool.and(Bool.not(String.eq(new, old)), Bool.or(_, Bool.not(String.eq(new, base)))),
        name, old, new, rest) == rest : List<&2, Mv.Shift>}
  %Equal.sym(Bool, String.eq(new, base), True{}, eb)
    : {Mv.move.put(Bool.and(Bool.not(String.eq(new, old)), Bool.not(_)), name, old, new, rest) == rest
      : List<&2, Mv.Shift>}
  %Equal.sym(Bool, Bool.and(Bool.not(String.eq(new, old)), False{}), False{},
    Str.and_false(Bool.not(String.eq(new, old))))
    : {Mv.move.put(_, name, old, new, rest) == rest : List<&2, Mv.Shift>}
  {==}

def Laws.rewrite_reimports(_ss, _at, _text, _tl):
  {==}

def Laws.round_walks_again(_text, _fs, _files, _old, _base, _only, _ms):
  {==}

def Laws.cascade_stops(fuel, ctx, ms, es):
  %Equal.sym(Bool, Mv.moves.eq(ms, Mv.round(ctx, ms)), True{}, es)
    : {Mv.cascade.pick(_, ms, _u => Mv.cascade.go(fuel, ctx, Mv.round(ctx, ms))) == ms : List<&2, Mv.Shift>}
  {==}

def Laws.cascade_goes_on(fuel, ctx, ms, es):
  %Equal.sym(Bool, Mv.moves.eq(ms, Mv.round(ctx, ms)), False{}, es)
    : {Mv.cascade.pick(_, ms, _u => Mv.cascade.go(fuel, ctx, Mv.round(ctx, ms)))
      == Mv.cascade.go(fuel, ctx, Mv.round(ctx, ms)) : List<&2, Mv.Shift>}
  {==}

def Laws.up_plans_moved(text, _spec, fs, lock, world, ev):
  %Equal.sym(Bool, W.args.upgrade(world), True{}, ev)
    : {UUp.world.at(_, text, fs, lock, world)
      == Mv.world.moved(
        J.joint(text, fs, Mv.rewrite(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, UUp.files.of(world), lock,
          W.args.only(world)))), UUp.files.of(world))),
        Mv.rewrite(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, UUp.files.of(world), lock, W.args.only(world)))),
          UUp.files.of(world)),
        world) : W.World}
  {==}

def Laws.edits_write_changed(ss, at, text, tl, ec, el):
  %Equal.sym(Bool, String.eq(U.reimport.many(ss, text), text), False{}, ec)
    : {Mv.edit.put(Bool.not(_), at, U.reimport.many(ss, text), Mv.edits(ss, tl))
      == P.Write{at, U.reimport.many(ss, text)} <> Mv.edits(ss, tl) : List<&2, P.Effect>}
  %Equal.sym(Bool, String.eq(at, P.lockfile()), False{}, el)
    : {Bool.pick(List<&2, P.Effect>, _, Mv.edits(ss, tl), P.Write{at, U.reimport.many(ss, text)} <> Mv.edits(ss, tl))
      == P.Write{at, U.reimport.many(ss, text)} <> Mv.edits(ss, tl) : List<&2, P.Effect>}
  {==}

def Laws.edits_skip_unchanged(ss, at, text, tl, ec):
  %Equal.sym(Bool, String.eq(U.reimport.many(ss, text), text), True{}, ec)
    : {Mv.edit.put(Bool.not(_), at, U.reimport.many(ss, text), Mv.edits(ss, tl)) == Mv.edits(ss, tl)
      : List<&2, P.Effect>}
  {==}

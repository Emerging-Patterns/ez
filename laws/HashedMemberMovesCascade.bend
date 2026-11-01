# A member whose ledger gives neither is imported by its `0x` hash. A plain
# `ez lock` refuses, asking nothing and writing nothing, when an import line
# names the hash the lock being rewritten records for a member whose hash
# has since moved, and names `ez lock --upgrade --package <name>`. That
# upgrade rewrites every such line as laws/UpgradeRewritesImports.bend and
# laws/RewriteKeepsOtherLines.bend rewrite a moved dependency's, and moves
# in turn every member imported by hash whose files it rewrote, until no
# import line names a moved member's old hash.
#
# also rests on: laws/UpRefusalWritesNothing.bend, laws/UpWritesTheLock.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/ledger/upgrade.bend as U
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../src/ws/up.bend as UUp
import ../src/ws/moved.bend as Mv

# ---------------------------------------------------------------------------
# a member imported by its hash, once it moved
# (laws/HashedMemberMovesCascade.bend)

# LAW: a plain lock at a workspace root with a committed line naming the hash
# the lock being rewritten records for a member that has moved since refuses
# with why, writing nothing
law stale_plain_refuses:
  for +text: String
  for +spec: WWorkspace.Spec
  for +fs: List<&2, J.Found>
  for +lock: String
  for +world: W.World
  for +why: String
  for ev: {W.args.upgrade(world) == False{} : Bool}
  for ew: {Mv.stale.world(lock, world) == why : String}
  for en: {String.is_empty(why) == False{} : Bool}
  {UUp.plan(UUp.Back{text, spec, fs, lock}, world) == P.Plan{[], P.Refused{why}} : P.Plan}

# LAW: and it asks nothing first
law stale_plain_asks_nothing:
  for +text: String
  for +spec: WWorkspace.Spec
  for +fs: List<&2, J.Found>
  for +lock: String
  for +world: W.World
  for +why: String
  for ev: {W.args.upgrade(world) == False{} : Bool}
  for ew: {Mv.stale.world(lock, world) == why : String}
  for en: {String.is_empty(why) == False{} : Bool}
  {UUp.step(UUp.Back{text, spec, fs, lock}, world) == P.Run{P.Plan{[], P.Refused{why}}} : P.Step}

# LAW: a file whose line names a moved member's recorded hash is the one the
# refusal names, with the member and the upgrade that rewrites the line
law stale_names_upgrade:
  for +name: String
  for +old: String
  for +new: String
  for rest: List<&2, Mv.Shift>
  for +at: String
  for +text: String
  for eh: {String.eq(U.reimport.many([U.Swap{old, new}], text), text) == False{} : Bool}
  {Mv.stale.moves(Mv.Shift{name, old, new} <> rest, at, text)
    == "ez: " ++ at ++ " imports workspace member " ++ name ++ " by " ++ old ++
      ", the hash the lock records for it, and the member is " ++ new ++
      " now; ez lock --upgrade --package " ++ name ++ " rewrites the import" : String}

# LAW: and a move no line of the file names is passed over
law stale_skips_move:
  for +name: String
  for +old: String
  for +new: String
  for +rest: List<&2, Mv.Shift>
  for +at: String
  for +text: String
  for eh: {String.eq(U.reimport.many([U.Swap{old, new}], text), text) == True{} : Bool}
  {Mv.stale.moves(Mv.Shift{name, old, new} <> rest, at, text) == Mv.stale.moves(rest, at, text) : String}

# LAW: the first committed file that names a moved member's recorded hash
# stops the lock
law stale_first_file:
  for +ms: List<&2, Mv.Shift>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  for +why: String
  for eh: {Mv.stale.moves(ms, at, text) == why : String}
  for en: {String.is_empty(why) == False{} : Bool}
  {Mv.stale(ms, K.Source{at, text} <> tl) == why : String}

# LAW: and a file that names none is passed over
law stale_skips_file:
  for +ms: List<&2, Mv.Shift>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  for eh: {Mv.stale.moves(ms, at, text) == "" : String}
  {Mv.stale(ms, K.Source{at, text} <> tl) == Mv.stale(ms, tl) : String}

# LAW: a member the lock records moves when its hash is not the one the lock
# records and it is chosen: every member for a plain lock and for an upgrade
# with no `--package`, the one named otherwise
law move_chosen:
  for +path: String
  for +name: String
  for +new: String
  for +base: String
  for +old: String
  for +only: String
  for +rest: List<&2, Mv.Shift>
  for eo: {String.eq(new, old) == False{} : Bool}
  for ec: {U.chosen(only, name) == True{} : Bool}
  {Mv.move.found(Some{Mv.Held{path, name, new}}, base, old, only, rest) == Mv.Shift{name, old, new} <> rest
    : List<&2, Mv.Shift>}

# LAW: and so does one that is not chosen once the upgrade rewrote its files,
# which moved its hash from the one it had before any line was rewritten
law move_rewritten:
  for +path: String
  for +name: String
  for +new: String
  for +base: String
  for +old: String
  for +only: String
  for +rest: List<&2, Mv.Shift>
  for eo: {String.eq(new, old) == False{} : Bool}
  for ec: {U.chosen(only, name) == False{} : Bool}
  for eb: {String.eq(new, base) == False{} : Bool}
  {Mv.move.found(Some{Mv.Held{path, name, new}}, base, old, only, rest) == Mv.Shift{name, old, new} <> rest
    : List<&2, Mv.Shift>}

# LAW: a member whose hash is the one the lock records does not move
law move_same:
  for +path: String
  for +name: String
  for +new: String
  for +base: String
  for +old: String
  for +only: String
  for +rest: List<&2, Mv.Shift>
  for eo: {String.eq(new, old) == True{} : Bool}
  {Mv.move.found(Some{Mv.Held{path, name, new}}, base, old, only, rest) == rest : List<&2, Mv.Shift>}

# LAW: nor does one not chosen whose files the upgrade did not rewrite
law move_untouched:
  for +path: String
  for +name: String
  for +new: String
  for +base: String
  for +old: String
  for +only: String
  for +rest: List<&2, Mv.Shift>
  for ec: {U.chosen(only, name) == False{} : Bool}
  for eb: {String.eq(new, base) == True{} : Bool}
  {Mv.move.found(Some{Mv.Held{path, name, new}}, base, old, only, rest) == rest : List<&2, Mv.Shift>}

# LAW: a round of the upgrade rewrites every committed line naming a moved
# member's recorded hash, as an upgrade rewrites a moved dependency's
# (`U.reimport.many`, laws/UpgradeRewritesImports.bend,
# laws/RewriteKeepsOtherLines.bend), from the files as they were
law rewrite_reimports:
  for +ss: List<&2, U.Swap>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  {Mv.rewrite(ss, K.Source{at, text} <> tl) == K.Source{at, U.reimport.many(ss, text)} <> Mv.rewrite(ss, tl)
    : List<&2, K.Source>}

# LAW: and walks every member again over them, for the moves the next round
# makes
law round_walks_again:
  for +text: String
  for +fs: List<&2, J.Found>
  for +files: List<&2, K.Source>
  for +old: List<&2, Mv.Held>
  for +base: List<&2, Mv.Held>
  for +only: String
  for +ms: List<&2, Mv.Shift>
  {Mv.round(Mv.Ctx{text, fs, files, old, base, only}, ms)
    == Mv.moves(old, Mv.now(J.joint(text, fs, Mv.rewrite(Mv.swaps(ms), files))), base, only)
    : List<&2, Mv.Shift>}

# LAW: the rounds stop at the first that moves no member further
law cascade_stops:
  for fuel: Nat
  for +ctx: Mv.Ctx
  for +ms: List<&2, Mv.Shift>
  for es: {Mv.moves.eq(ms, Mv.round(ctx, ms)) == True{} : Bool}
  {Mv.cascade.go((1n + fuel : Nat), ctx, ms) == ms : List<&2, Mv.Shift>}

# LAW: and go on from one that does
law cascade_goes_on:
  for fuel: Nat
  for +ctx: Mv.Ctx
  for +ms: List<&2, Mv.Shift>
  for es: {Mv.moves.eq(ms, Mv.round(ctx, ms)) == False{} : Bool}
  {Mv.cascade.go((1n + fuel : Nat), ctx, ms) == Mv.cascade.go(fuel, ctx, Mv.round(ctx, ms)) : List<&2, Mv.Shift>}

# LAW: an upgrade at a workspace root plans on the committed files rewritten
# with every move, the joint ledger and its members' answers made again over
# them
law up_plans_moved:
  for +text: String
  for spec: WWorkspace.Spec
  for +fs: List<&2, J.Found>
  for +lock: String
  for +world: W.World
  for ev: {W.args.upgrade(world) == True{} : Bool}
  {UUp.plans.on(UUp.Back{text, spec, fs, lock}, world)
    == Mv.world.moved(
      J.joint(text, fs, Mv.rewrite(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, UUp.files.of(world), lock,
        W.args.only(world)))), UUp.files.of(world))),
      Mv.rewrite(Mv.swaps(Mv.cascade(Mv.ctx(text, fs, UUp.files.of(world), lock, W.args.only(world)))),
        UUp.files.of(world)),
      world) : W.World}

# LAW: and writes every committed file a move changes, with its lines
# rewritten
law edits_write_changed:
  for +ss: List<&2, U.Swap>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  for ec: {String.eq(U.reimport.many(ss, text), text) == False{} : Bool}
  for el: {String.eq(at, P.lockfile()) == False{} : Bool}
  {Mv.edits(ss, K.Source{at, text} <> tl) == P.Write{at, U.reimport.many(ss, text)} <> Mv.edits(ss, tl)
    : List<&2, P.Effect>}

# LAW: and none it leaves as it was
law edits_skip_unchanged:
  for +ss: List<&2, U.Swap>
  for +at: String
  for +text: String
  for +tl: List<&2, K.Source>
  for ec: {String.eq(U.reimport.many(ss, text), text) == True{} : Bool}
  {Mv.edits(ss, K.Source{at, text} <> tl) == Mv.edits(ss, tl) : List<&2, P.Effect>}

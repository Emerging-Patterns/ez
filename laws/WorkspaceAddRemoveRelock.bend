# In a workspace, at its root or in a member, `ez add` and `ez remove` keep
# the root's ez.lock.toml in step with the ledger they write, in one plan: one
# that succeeds runs its own effects, a root's ledger keeping its
# `[workspace]` table, and then exactly the plan a plain `ez lock` at the root
# makes on the workspace it leaves, which is the root's ledger and every
# member's with the one the command writes in place of its own, the `.bend`
# files git lists under the root, and the answers the lock is given, with
# every path that plan writes taken from the root, so no lock is written in a
# member. When the ledgers it leaves cannot be joined, or that lock refuses,
# the command refuses and writes nothing. Outside a workspace it runs the plan
# laws/AddRemoveRelock.bend says.
#
# also rests on: laws/AddWsRefusalWritesNothing.bend,
# laws/RemoveWsRefusalWritesNothing.bend
import Base
import ../src/pkg/path.bend as Path
import ../src/ledger/manifest.bend as M
import ../src/ledger/render.bend as Rend
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W
import ../src/add/world.bend as A
import ../src/add/relock.bend as AR
import ../src/relock/relock.bend as R
import ../src/remove/plan.bend as RP
import ../src/remove/relock.bend as RR
import ../src/ws/workspace.bend as WWorkspace
import ../src/ws/joint.bend as J
import ../src/ws/up.bend as UUp
import ../src/ws/relock.bend as Rel

# ---------------------------------------------------------------------------
# `ez add` and `ez remove` in a workspace (ws/relock.bend)

# LAW: an effect of the root's lock writes a file at its path from the root
law at_write:
  for +at: String
  for path: String
  for text: String
  {Rel.at.effect(at, P.Write{path, text}) == P.Write{Path.join(at, path), text} : P.Effect}

# LAW: lays a committed tree in the root's `.ez/lib`
law at_committed:
  for +at: String
  for hash: String
  for fs: List<&2, W.Source>
  {Rel.at.effect(at, P.Lay{P.Committed{}, hash, fs}) == P.Lay{P.Under{at}, hash, fs} : P.Effect}

# LAW: lays any other tree in BEND_LIB as it is
law at_cache:
  for +at: String
  for hash: String
  for fs: List<&2, W.Source>
  {Rel.at.effect(at, P.Lay{P.Cache{}, hash, fs}) == P.Lay{P.Cache{}, hash, fs} : P.Effect}

# LAW: removes a committed tree from the root's `.ez/lib`
law at_drop:
  for +at: String
  for hash: String
  {Rel.at.effect(at, P.Drop{hash}) == P.Lay{P.Under{at}, hash, []} : P.Effect}

# LAW: and says what it says as it is
law at_say:
  for +at: String
  for text: String
  {Rel.at.effect(at, P.Say{text}) == P.Say{text} : P.Effect}

# LAW: and writes a names file in BEND_LIB as it is
law at_name:
  for +at: String
  for nv: String
  for hash: String
  {Rel.at.effect(at, P.Name{nv, hash}) == P.Name{nv, hash} : P.Effect}

# LAW: the root's lock runs every effect of its plan, so, in order
law at_plan_effects:
  for +at: String
  for pl: P.Plan
  {P.effects(Rel.at.plan(at, pl)) == Rel.at.effects(at, P.effects(pl)) : List<&2, P.Effect>}

# LAW: and refuses exactly when its plan does
law at_plan_refuses:
  for +at: String
  for pl: P.Plan
  {R.refuses(Rel.at.plan(at, pl)) == R.refuses(pl) : Bool}

# LAW: a ledger written at a workspace root keeps the root's `[workspace]`
# table, written back as an upgrade writes the root's ledger
law keep_root:
  for +old: String
  for +text: String
  for +spec: WWorkspace.Spec
  for +mm: M.Manifest
  for ws: {WWorkspace.spec.of(old) == WWorkspace.Root{spec} : WWorkspace.Read}
  for rd: {M.parse(text) == M.Good{mm} : M.Read}
  {Rel.keep(old, text) == UUp.root.text(mm, spec, WWorkspace.root.of(old)) : String}

# LAW: and a root with no `[workspace]` table is written as it is
law keep_lone:
  for +old: String
  for +text: String
  for ws: {WWorkspace.spec.of(old) == WWorkspace.Lone{} : WWorkspace.Read}
  {Rel.keep(old, text) == text : String}

# LAW: at the root, the command's write of ez.toml is kept so
law keep_ledger_write:
  for +old: String
  for text: String
  {Rel.keep.effect(old, P.Write{"ez.toml", text}) == P.Write{"ez.toml", Rel.keep(old, text)} : P.Effect}

# LAW: and every other file it writes is written as it is
law keep_other_write:
  for +old: String
  for +path: String
  for text: String
  for other: {String.eq(path, "ez.toml") == False{} : Bool}
  {Rel.keep.effect(old, P.Write{path, text}) == P.Write{path, text} : P.Effect}

# LAW: the command's own plan at the root is every effect so kept, ending as
# it ends
law edit_root:
  for +old: String
  for es: List<&2, P.Effect>
  for outcome: P.Outcome
  {Rel.edit.at([], old, P.Plan{es, outcome}) == P.Plan{Rel.keep.effects(old, es), outcome} : P.Plan}

# LAW: and in a member it is the command's own plan as it is
law edit_member:
  for hd: String
  for tl: List<&2, String>
  for +old: String
  for pl: P.Plan
  {Rel.edit.at(hd <> tl, old, pl) == pl : P.Plan}

# LAW: the ledgers a command at the root leaves are the one it writes as the
# root's, and every other as git lists it
law ledgers_root:
  for +new: String
  for +text: String
  for +fs: List<&2, J.Found>
  {Rel.ledgers.at([], new, text, fs) == Rel.Ledgers{new, fs} : Rel.Ledgers}

# LAW: and those a command in a member leaves are the root's, and every
# other, the member's ez.toml holding the one it writes
law ledgers_member:
  for hd: String
  for tl: List<&2, String>
  for +new: String
  for +text: String
  for +fs: List<&2, J.Found>
  {Rel.ledgers.at(hd <> tl, new, text, fs)
    == Rel.Ledgers{text, Rel.put.found(fs, Path.join(WWorkspace.segs.text(hd <> tl), "ez.toml"), new)} : Rel.Ledgers}

# LAW: a listed ez.toml at that path holds the text the command writes
law put_found_hit:
  for +path: String
  for was: String
  for tl: List<&2, J.Found>
  for +text: String
  {Rel.put.found(J.Found{path, was} <> tl, path, text) == J.Found{path, text} <> Rel.put.found(tl, path, text)
    : List<&2, J.Found>}

# LAW: and every other holds what it held
law put_found_miss:
  for +fp: String
  for was: String
  for tl: List<&2, J.Found>
  for +path: String
  for +text: String
  for other: {String.eq(fp, path) == False{} : Bool}
  {Rel.put.found(J.Found{fp, was} <> tl, path, text) == J.Found{fp, was} <> Rel.put.found(tl, path, text)
    : List<&2, J.Found>}

# LAW: the ledger the command writes is the one those ledgers hold
law ledgers_write:
  for at: String
  for rel: List<&2, String>
  for +text: String
  for fs: List<&2, J.Found>
  for listing: W.Listing
  for lock: String
  for pl: P.Plan
  for was: Maybe<&2, String>
  for +new: String
  for put: {P.put.plan(pl, "ez.toml") == P.Put{new} : P.Wrote}
  {Rel.ledgers(Rel.Rooted{at, rel, text, fs, listing, lock}, pl, was) == Rel.ledgers.at(rel, new, text, fs)
    : Rel.Ledgers}

# LAW: the lock over those ledgers is exactly the plan a plain `ez lock` at the
# root makes: on the joint ledger, with what an upgrade needs to write each
# ledger back, and on a plain lock's World at the root's directory holding the
# members' answers ahead of the rest
law lock_root_plain:
  for +at: String
  for rel: List<&2, String>
  for was: String
  for found: List<&2, J.Found>
  for +listing: W.Listing
  for +lock: String
  for +text: String
  for +fs: List<&2, J.Found>
  for rs: List<&2, W.Reply>
  for +spec: WWorkspace.Spec
  for +mm: M.Manifest
  for ws: {WWorkspace.spec.of(text) == WWorkspace.Root{spec} : WWorkspace.Read}
  for jj: {J.joint(text, fs, J.files(listing)) == J.Joint{mm} : J.Joint}
  {Rel.lock.plan(Rel.lock.of(Rel.Ledgers{text, fs}, Rel.Rooted{at, rel, was, found, listing, lock}, rs))
    == UUp.plan(UUp.Back{text, spec, fs, lock}, W.World{W.Args{False{}, "", at}, Some{Rend.show(mm)}, listing,
      List.append(&2, W.Reply, J.seeds(J.Joint{mm}, J.files(listing)), rs), []}) : P.Plan}

# LAW: and when those ledgers cannot be joined it refuses with why, with no
# effect
law lock_root_clash:
  for +at: String
  for rel: List<&2, String>
  for was: String
  for found: List<&2, J.Found>
  for +listing: W.Listing
  for +lock: String
  for +text: String
  for +fs: List<&2, J.Found>
  for rs: List<&2, W.Reply>
  for +spec: WWorkspace.Spec
  for +why: String
  for ws: {WWorkspace.spec.of(text) == WWorkspace.Root{spec} : WWorkspace.Read}
  for jj: {J.joint(text, fs, J.files(listing)) == J.Clash{why} : J.Joint}
  {Rel.lock.plan(Rel.lock.of(Rel.Ledgers{text, fs}, Rel.Rooted{at, rel, was, found, listing, lock}, rs))
    == P.Plan{[], P.Refused{why}} : P.Plan}

# LAW: as it does when the root's `[workspace]` table cannot be read
law lock_root_bad:
  for +at: String
  for rel: List<&2, String>
  for was: String
  for found: List<&2, J.Found>
  for +listing: W.Listing
  for +lock: String
  for +text: String
  for +fs: List<&2, J.Found>
  for rs: List<&2, W.Reply>
  for +why: String
  for ws: {WWorkspace.spec.of(text) == WWorkspace.Bad{why} : WWorkspace.Read}
  {Rel.lock.plan(Rel.lock.of(Rel.Ledgers{text, fs}, Rel.Rooted{at, rel, was, found, listing, lock}, rs))
    == P.Plan{[], P.Refused{why}} : P.Plan}

# LAW: `ez add` in a workspace locks the ledgers its own plan leaves, with the
# answers it has for the lock ahead of the lock's own
law add_ws_locks_what_it_writes:
  for +root: Rel.Rooted
  for +aw: A.World
  for listing: W.Listing
  for locks: List<&2, W.Reply>
  {Rel.add.lock(root, AR.World{aw, listing, locks}) == Rel.lock.of(Rel.ledgers(root, Rel.add.edit(root, aw),
    A.ledger(aw)), root, List.append(&2, W.Reply, AR.seeds(aw), locks)) : Rel.Lock}

# LAW: `ez add` in a workspace that succeeds runs the add's effects as the
# workspace runs them, then the note, then exactly the effects of that lock,
# each written from the root
law add_ws_runs_add_then_lock:
  for +root: Rel.Rooted
  for +w: AR.World
  for ok: {R.refuses(Rel.add.plan(root, w)) == False{} : Bool}
  {P.effects(Rel.add.plan(root, w)) == List.append(&2, P.Effect, P.effects(Rel.add.edit(root, AR.add(w))),
    List.append(&2, P.Effect, Rel.add.notes(Rel.add.lock(root, w), AR.add(w)),
      P.effects(Rel.at.plan(Rel.rooted.at(root), Rel.lock.plan(Rel.add.lock(root, w))))))
    : List<&2, P.Effect>}

# LAW: when that lock refuses, `ez add` refuses
law add_ws_refuses_with_lock:
  for +root: Rel.Rooted
  for +w: AR.World
  for r: {R.refuses(Rel.lock.plan(Rel.add.lock(root, w))) == True{} : Bool}
  {R.refuses(Rel.add.plan(root, w)) == True{} : Bool}

# LAW: the note says whether the root's lock holds the package added
law add_ws_notes:
  for back: UUp.Back
  for +world: W.World
  for +aw: A.World
  {Rel.add.notes(Rel.Lock{back, world}, aw) == AR.notes.of(AR.held(P.packs(world), AR.added(aw)), AR.added(aw))
    : List<&2, P.Effect>}

# LAW: in a project of its own `ez add` runs the plan
# laws/AddRemoveRelock.bend says
law add_own:
  for +w: AR.World
  {Rel.add.planned(Rel.Own{}, w) == AR.plan(w) : P.Plan}

# LAW: and asks what it asks
law add_own_next:
  for +w: AR.World
  {Rel.add.next(Rel.Own{}, w) == AR.next(w) : AR.Next}

# LAW: and in a workspace, the add and the root's lock
law add_inside:
  for +root: Rel.Rooted
  for +w: AR.World
  {Rel.add.planned(Rel.Inside{root}, w) == Rel.add.plan(root, w) : P.Plan}

# LAW: `ez remove` in a workspace locks the ledgers its own plan leaves
law remove_ws_locks_what_it_writes:
  for +root: Rel.Rooted
  for +rw: RP.World
  for here: String
  for listing: W.Listing
  for locks: List<&2, W.Reply>
  {Rel.remove.lock(root, RR.World{rw, here, listing, locks}) == Rel.lock.of(Rel.ledgers(root,
    Rel.remove.edit(root, rw), RR.ledger.was(rw)), root, locks) : Rel.Lock}

# LAW: `ez remove` in a workspace that succeeds runs the remove's effects as
# the workspace runs them, then exactly the effects of that lock, each
# written from the root
law remove_ws_runs_remove_then_lock:
  for +root: Rel.Rooted
  for +w: RR.World
  for ok: {R.refuses(Rel.remove.plan(root, w)) == False{} : Bool}
  {P.effects(Rel.remove.plan(root, w)) == List.append(&2, P.Effect,
    P.effects(Rel.remove.edit(root, RR.remove(w))),
    P.effects(Rel.at.plan(Rel.rooted.at(root), Rel.lock.plan(Rel.remove.lock(root, w))))) : List<&2, P.Effect>}

# LAW: when that lock refuses, `ez remove` refuses
law remove_ws_refuses_with_lock:
  for +root: Rel.Rooted
  for +w: RR.World
  for r: {R.refuses(Rel.lock.plan(Rel.remove.lock(root, w))) == True{} : Bool}
  {R.refuses(Rel.remove.plan(root, w)) == True{} : Bool}

# LAW: in a project of its own `ez remove` runs the plan
# laws/AddRemoveRelock.bend says
law remove_own:
  for +w: RR.World
  {Rel.remove.planned(Rel.Own{}, w) == RR.plan(w) : P.Plan}

# LAW: and asks what it asks
law remove_own_next:
  for +w: RR.World
  {Rel.remove.next(Rel.Own{}, w) == RR.next(w) : RR.Next}

# LAW: and in a workspace, the remove and the root's lock
law remove_inside:
  for +root: Rel.Rooted
  for +w: RR.World
  {Rel.remove.planned(Rel.Inside{root}, w) == Rel.remove.plan(root, w) : P.Plan}

# proofs of laws/WorkspaceAddRefusalWritesNothing.bend
import Base
import ../src/add/relock.bend as AR
import ../src/ws/relock.bend as Rel
import ../laws/WorkspaceAddRefusalWritesNothing.bend as Laws
import ./lemmas/JoinedPlanRefusals.bend as M1

def Laws.add_ws_refusal_writes_nothing(root, w, r):
  match w:
    case AR.World{+a, +listing, +locks}:
      M1.join_quiet(Rel.add.edit(root, a),
        Rel.at.plan(Rel.rooted.at(root), Rel.lock.plan(Rel.add.lock(root, AR.World{a, listing, locks}))),
        Rel.add.notes(Rel.add.lock(root, AR.World{a, listing, locks}), a), AR.tail(a), r)

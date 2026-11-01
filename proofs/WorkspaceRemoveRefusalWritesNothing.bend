# proofs of laws/WorkspaceRemoveRefusalWritesNothing.bend
import Base
import ../src/remove/relock.bend as RR
import ../src/ws/relock.bend as Rel
import ../laws/WorkspaceRemoveRefusalWritesNothing.bend as Laws
import ./lemmas/JoinedPlanRefusals.bend as M1

def Laws.remove_ws_refusal_writes_nothing(root, w, rf):
  match w:
    case RR.World{+r, +here, +listing, +locks}:
      M1.join_quiet(Rel.remove.edit(root, r),
        Rel.at.plan(Rel.rooted.at(root), Rel.lock.plan(Rel.remove.lock(root, RR.World{r, here, listing, locks}))),
        [], RR.tail(), rf)

# proofs of laws/AddRemoveRelock.bend
import Base
import ../src/relock/relock.bend as R
import ../src/lock/plan.bend as P
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../src/add/relock.bend as AR
import ../src/remove/plan.bend as RP
import ../src/remove/relock.bend as RR
import ../laws/AddRemoveRelock.bend as Laws
import ./lemmas/AddPlanEffects.bend as M1

# ---------------------------------------------------------------------------
# laws/AddRemoveRelock.bend and laws/AddNotesUnlockedPackage.bend: the add
# and the lock as one plan

def Laws.add_runs_add_then_lock(w, ok):
  match w:
    case AR.World{+a, +listing, +locks}:
      M1.join_effects(AP.command(a), AR.lock(AR.World{a, listing, locks}),
        AR.notes(AR.World{a, listing, locks}), AR.tail(a), ok)

def Laws.add_locks_what_it_writes(w, text, put):
  match w:
    case AR.World{+a, _listing, _locks}:
      %Equal.sym(P.Wrote, P.put.plan(AP.command(a), "ez.toml"), P.Put{text}, put)
        : {R.ledger.of(_, A.ledger(a)) == Some{text} : Maybe<&2, String>}
      {==}

def Laws.add_relock_is_plain(w):
  match w:
    case AR.World{_a, _listing, _locks}:
      {==}

def Laws.add_refuses_with_lock(w, r):
  match w:
    case AR.World{+a, +listing, +locks}:
      M1.join_refuses_lock(AP.command(a), AR.lock(AR.World{a, listing, locks}),
        AR.notes(AR.World{a, listing, locks}), AR.tail(a), r)

# ---------------------------------------------------------------------------
# laws/AddRemoveRelock.bend: the remove and the lock as one plan

def Laws.remove_runs_remove_then_lock(w, ok):
  match w:
    case RR.World{+r, +here, +listing, +locks}:
      M1.join_effects(RP.plan(r), RR.lock(RR.World{r, here, listing, locks}), [], RR.tail(), ok)

def Laws.remove_locks_what_it_writes(w, text, put):
  match w:
    case RR.World{+r, +here, _listing, _locks}:
      %Equal.sym(P.Wrote, P.put.plan(RP.plan(r), "ez.toml"), P.Put{text}, put)
        : {R.ledger.of(_, RR.ledger.was(r)) == Some{text} : Maybe<&2, String>}
      {==}

def Laws.remove_relock_is_plain(w):
  match w:
    case RR.World{_r, _here, _listing, _locks}:
      {==}

def Laws.remove_refuses_with_lock(w, r):
  match w:
    case RR.World{+rm, +here, +listing, +locks}:
      M1.join_refuses_lock(RP.plan(rm), RR.lock(RR.World{rm, here, listing, locks}), [],
        RR.tail(), r)

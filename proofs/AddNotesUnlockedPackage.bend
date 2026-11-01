# proofs of laws/AddNotesUnlockedPackage.bend
import Base
import ../src/lock/plan.bend as P
import ../src/add/relock.bend as AR
import ../laws/AddNotesUnlockedPackage.bend as Laws

def Laws.add_notes_unlocked(w, no):
  %Equal.sym(Bool, AR.held(P.packs(AR.lock.world(w)), AR.added(AR.add(w))), False{}, no)
    : {AR.notes.of(_, AR.added(AR.add(w))) == [P.Say{AR.unlocked(AR.added(AR.add(w)))}]
    : List<&2, P.Effect>}
  {==}

def Laws.add_notes_nothing_when_locked(w, yes):
  %Equal.sym(Bool, AR.held(P.packs(AR.lock.world(w)), AR.added(AR.add(w))), True{}, yes)
    : {AR.notes.of(_, AR.added(AR.add(w))) == [] : List<&2, P.Effect>}
  {==}

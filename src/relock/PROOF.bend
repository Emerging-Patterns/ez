# relock: the proofs of what joining an edit to the lock does, for every
# edit, lock, note and tail. `ez add` and `ez remove` (add/PROOF.bend,
# remove/PROOF.bend) prove their EZ-DOC-6 laws from these. `bend PROOF.bend`
# is the gate.
import Base
import ./relock.bend as R
import ../lock/plan.bend as P
import ../check/eq.bend as Eq

# LAW: a lock that refuses after an edit that succeeded writes nothing
law lock_quiet:
  for l: P.Plan
  for +e: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for r: {R.refuses(R.join.lock(l, e, n, t)) == True{} : Bool}
  {P.writes(R.join.lock(l, e, n, t)) == False{} : Bool}

def lock_quiet(l, e, n, t, r):
  match l:
    case P.Plan{es, o}:
      match o:
        case P.Success{}:
          Eq.bit.absurd(&2, {P.writes(R.join.lock(P.Plan{es, P.Success{}}, e, n, t))
            == False{} : Bool}, r)
        case P.Refused{_why}:
          {==}

# LAW: a joined plan that refuses writes nothing, whichever half refused
law edit_quiet:
  for b: Bool
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for r: {R.refuses(R.join.edit(b, e, l, n, t)) == True{} : Bool}
  {P.writes(R.join.edit(b, e, l, n, t)) == False{} : Bool}

def edit_quiet(b, e, l, n, t, r):
  match b:
    case True{}:
      {==}
    case False{}:
      lock_quiet(l, e, n, t, r)

law join_quiet:
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for r: {R.refuses(R.join(e, l, n, t)) == True{} : Bool}
  {P.writes(R.join(e, l, n, t)) == False{} : Bool}

def join_quiet(e, l, n, t, r):
  edit_quiet(R.refuses(e), e, l, n, t, r)

# LAW: a lock that succeeds after an edit that succeeded runs the edit's
# effects, the notes and the lock's effects, in that order
law lock_effects:
  for l: P.Plan
  for +e: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for ok: {R.refuses(R.join.lock(l, e, n, t)) == False{} : Bool}
  {P.effects(R.join.lock(l, e, n, t)) == List.append(&2, P.Effect, P.effects(e),
    List.append(&2, P.Effect, n, P.effects(l))) : List<&2, P.Effect>}

def lock_effects(l, e, n, t, ok):
  match l:
    case P.Plan{es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{why}:
          Eq.bit.absurd2(&2, {P.effects(R.join.lock(P.Plan{es, P.Refused{why}}, e, n, t))
            == List.append(&2, P.Effect, P.effects(e),
              List.append(&2, P.Effect, n, P.effects(P.Plan{es, P.Refused{why}})))
            : List<&2, P.Effect>}, ok)

law edit_effects:
  for b: Bool
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for ok: {R.refuses(R.join.edit(b, e, l, n, t)) == False{} : Bool}
  {P.effects(R.join.edit(b, e, l, n, t)) == List.append(&2, P.Effect, P.effects(e),
    List.append(&2, P.Effect, n, P.effects(l))) : List<&2, P.Effect>}

def edit_effects(b, e, l, n, t, ok):
  match b:
    case True{}:
      Eq.bit.absurd2(&2, {P.effects(R.join.edit(True{}, e, l, n, t))
        == List.append(&2, P.Effect, P.effects(e), List.append(&2, P.Effect, n, P.effects(l)))
        : List<&2, P.Effect>}, ok)
    case False{}:
      lock_effects(l, e, n, t, ok)

# LAW: a joined plan that succeeds runs the edit's effects, the notes, and the
# lock's effects
law join_effects:
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for ok: {R.refuses(R.join(e, l, n, t)) == False{} : Bool}
  {P.effects(R.join(e, l, n, t)) == List.append(&2, P.Effect, P.effects(e),
    List.append(&2, P.Effect, n, P.effects(l))) : List<&2, P.Effect>}

def join_effects(e, l, n, t, ok):
  edit_effects(R.refuses(e), e, l, n, t, ok)

# LAW: a lock that refuses refuses the joined plan, whatever the edit did
law edit_refuses_lock:
  for b: Bool
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for r: {R.refuses(l) == True{} : Bool}
  {R.refuses(R.join.edit(b, e, l, n, t)) == True{} : Bool}

def edit_refuses_lock(b, e, l, n, t, r):
  match b:
    case True{}:
      {==}
    case False{}:
      match l:
        case P.Plan{es, o}:
          match o:
            case P.Success{}:
              Eq.bit.absurd(&2, {R.refuses(R.join.edit(False{}, e, P.Plan{es, P.Success{}}, n, t))
                == True{} : Bool}, r)
            case P.Refused{_why}:
              {==}

law join_refuses_lock:
  for +e: P.Plan
  for l: P.Plan
  for n: List<&2, P.Effect>
  for +t: String
  for r: {R.refuses(l) == True{} : Bool}
  {R.refuses(R.join(e, l, n, t)) == True{} : Bool}

def join_refuses_lock(e, l, n, t, r):
  edit_refuses_lock(R.refuses(e), e, l, n, t, r)

# LAW: a plan ends with the status of whether it refuses
law join_code:
  for pl: P.Plan
  {P.code(pl) == P.status.of(R.refuses(pl)) : U32}

def join_code(pl):
  match pl:
    case P.Plan{_es, o}:
      match o:
        case P.Success{}:
          {==}
        case P.Refused{_why}:
          {==}

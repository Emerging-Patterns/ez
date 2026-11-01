# a joined edit-and-lock plan that refuses writes nothing, whichever half
# refused
#
# The proofs of what joining an edit to the lock does, for every edit, lock,
# note and tail. `ez add` and `ez remove` prove their
# laws/AddRemoveRelock.bend laws from these.
import Base
import ../../src/check/eq.bend as Eq
import ../../src/relock/relock.bend as R
import ../../src/lock/plan.bend as P

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

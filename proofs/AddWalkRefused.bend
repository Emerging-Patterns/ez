# proofs of laws/AddWalkRefused.bend
import Base
import ../src/pkg/pkg.bend as K
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP
import ../laws/AddWalkRefused.bend as Laws
import ./lemmas/LockPlannerFacts.bend as M1

# LAW: a walk that refuses loses, whatever the entry lookup
law walk_loses:
  for g: Maybe<&2, String>
  for +w: A.World
  for +why: String
  for e: {AP.walked(w) == K.Refused{why} : K.Walked}
  {M1.win(AP.outcome.entry(g, AP.walked(w), w)) == False{} : Bool}

def walk_loses(g, w, why, e):
  match g:
    case None{}:
      {==}
    case Some{_t}:
      %Equal.sym(K.Walked, AP.walked(w), K.Refused{why}, e)
        : {M1.win(AP.outcome.walk(_, w)) == False{} : Bool}
      {==}

def Laws.add_walk_refused(w, why, e):
  M1.lose_v(AP.decide(w), w, walk_loses(M1.got(w), w, why, e))

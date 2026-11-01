import Base
import ../src/pkg/pkg.bend as K
import ../src/add/world.bend as A
import ../src/add/plan.bend as AP

# LAW: a walk that refuses, such as one whose imports climb out of the
# checkout, refuses the add
law add_walk_refused:
  for +w: A.World
  for +why: String
  for e: {AP.walked(w) == K.Refused{why} : K.Walked}
  {AP.refuses(w) == True{} : Bool}

# proofs of laws/ClimbsStack.bend
import Base
import ../src/add/world.bend as A
import ../laws/ClimbsStack.bend as Laws

# A climb against a kept climb asks the same question of two literals, so it
# computes and the law is closed.
def Laws.up_stacks(_abs, _t):
  {==}

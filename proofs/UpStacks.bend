# proofs of laws/UpStacks.bend
import Base
import ../src/add/world.bend as A
import ../laws/UpStacks.bend as Laws

# A climb against a kept climb asks the same question of two literals, so it
# computes and the law is closed.
def Laws.up_stacks(_abs, _t):
  {==}

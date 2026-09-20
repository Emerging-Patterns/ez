import Base
import ./util/math.bend as M
import ../other/up.bend as U

# four times the number
def quad(+x: U32) -> U32:
  M.double(M.double(x))

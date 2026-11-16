# proofs of laws/EnvFallsBack.bend
import Base
import ../src/share/env.bend as Env
import ../laws/EnvFallsBack.bend as Laws

# the pick reads the premise's answer
def Laws.value_kept(value, alt, full):
  Equal.cong(Bool, String, b => Bool.pick(String, b, alt, value),
    String.is_empty(value), False{}, full)

def Laws.empty_falls_back(_alt):
  {==}

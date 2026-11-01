# proofs of laws/DirsCheck.bend
import Base
import ../src/share/env.bend as Env
import ../laws/DirsCheck.bend as Laws

def Laws.dirs_check(cmd, out, ec):
  %ec : {Bool.pick(List<&2, String>, _, [".ez"],
    Env.dirs.build(String.eq(cmd, "build"), String.is_empty(out)))
    == [".ez"] : List<&2, String>}
  {==}

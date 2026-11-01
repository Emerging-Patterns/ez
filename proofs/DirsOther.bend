# proofs of laws/DirsOther.bend
import Base
import ../src/share/env.bend as Env
import ../laws/DirsOther.bend as Laws

# env: each premise is rewritten into the test the pick turns on.

def Laws.dirs_other(cmd, out, ec, eb):
  %ec : {Bool.pick(List<&2, String>, _, [".ez"],
    Env.dirs.build(String.eq(cmd, "build"), String.is_empty(out)))
    == [] : List<&2, String>}
  %eb : {Env.dirs.build(_, String.is_empty(out)) == [] : List<&2, String>}
  {==}

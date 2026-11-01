# proofs of laws/BuildWithOutMakesNothing.bend
import Base
import ../src/share/env.bend as Env
import ../laws/BuildWithOutMakesNothing.bend as Laws

def Laws.dirs_build_out(cmd, out, ec, eb, eo):
  %ec : {Bool.pick(List<&2, String>, _, [".ez"],
    Env.dirs.build(String.eq(cmd, "build"), String.is_empty(out)))
    == [] : List<&2, String>}
  %eb : {Env.dirs.build(_, String.is_empty(out)) == [] : List<&2, String>}
  %eo : {Bool.pick(List<&2, String>, _, ["bin"], []) == [] : List<&2, String>}
  {==}

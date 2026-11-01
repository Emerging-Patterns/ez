# proofs of laws/DirsBuild.bend
import Base
import ../src/share/env.bend as Env
import ../laws/DirsBuild.bend as Laws

def Laws.dirs_build(cmd, out, ec, eb, eo):
  %ec : {Bool.pick(List<&2, String>, _, [".ez"],
    Env.dirs.build(String.eq(cmd, "build"), String.is_empty(out)))
    == ["bin"] : List<&2, String>}
  %eb : {Env.dirs.build(_, String.is_empty(out)) == ["bin"] : List<&2, String>}
  %eo : {Bool.pick(List<&2, String>, _, ["bin"], []) == ["bin"]
    : List<&2, String>}
  {==}

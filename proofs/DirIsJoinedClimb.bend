# proofs of laws/DirIsJoinedClimb.bend
import Base
import ../src/pkg/path.bend as Path
import ../laws/DirIsJoinedClimb.bend as Laws

# `join` splices with a separator and normalises; `dir` splices a climb and
# normalises. With the directory known not to be empty the two splices are the
# same text.
def Laws.dir_is_climb(p, e):
  %e : {Path.dir(p) == Path.norm(Path.join.at(_, p, "..")) : String}
  {==}

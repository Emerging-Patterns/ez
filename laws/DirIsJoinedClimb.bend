import Base
import ../src/pkg/path.bend as Path

# LAW: taking the directory of a path is joining a climb onto it. `dir` is
# written as a splice and `join` as a normalisation of a splice, and this
# holds the one to the other, so the climb `pkg.place` takes is a join.
law dir_is_climb:
  for +p: String
  for e: {False{} == String.is_empty(p) : Bool}
  {Path.dir(p) == Path.join(p, "..") : String}

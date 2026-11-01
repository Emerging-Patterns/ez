import Base
import ../src/pkg/path.bend as Path
import ../src/add/world.bend as A
import ./defs/Slashless.bend as D1

# LAW: the directory of a single real component is here. A file with no
# slash in its name sits in the current directory, so climbing it off
# leaves `.` and not the empty string a join would write.
law dir_plain:
  for +p: String
  for +e: {D1.slashless(p) == True{} : Bool}
  for +e0: {False{} == String.is_empty(p) : Bool}
  for e1: {False{} == String.eq(p, ".") : Bool}
  for e2: {False{} == String.eq(p, "..") : Bool}
  {Path.dir(p) == "." : String}

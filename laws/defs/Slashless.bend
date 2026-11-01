# whether a string holds no `/`, and so is one component of a path
import Base
import ../../src/add/world.bend as A

# The path algebra, which is the other half of what a package's identity rests
# on: a module's name inside a package is the path it was reached through, and
# Base has no realpath, so `.` and `..` are resolved by text. A miscount there
# renames a module, and a renamed module is a different `0x` name.
#
# Two pieces of vocabulary the laws below need and nothing else uses. They
# say, in a form Bend can walk, what "this path holds no separator" means and
# which half of a half-finished normalisation is the root flag.

# whether a string holds no separator, and so is one component of a path
def slashless(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      Bool.and(Bool.not(Char.is_eq(h, '/')), slashless(t))

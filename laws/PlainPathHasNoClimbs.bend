import Base
import ../src/pkg/path.bend as Path
import ./defs/Slashless.bend as D1

# LAW: a path that holds no separator and is not a climb has no climbs.
# `pkg.place` re-roots by this count, so a file named in place does not
# lift the package.
law ups_plain:
  for +p: String
  for e: {D1.slashless(p) == True{} : Bool}
  for e2: {False{} == String.eq(p, "..") : Bool}
  {Path.ups(p) == 0n : Nat}

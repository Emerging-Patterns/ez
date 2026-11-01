import Base
import ../src/pkg/path.bend as Path

# LAW: a climb cancels the component it climbs off, whatever was kept before
# it and whether or not the path began at the root.
law up_cancels:
  for abs: Bool
  for +h: String
  for t: List<&2, String>
  for e: {False{} == String.eq(h, "..") : Bool}
  {Path.up(abs, h <> t) == t : List<&2, String>}

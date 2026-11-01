import Base
import ./defs/Slashless.bend as D1

# LAW: a path with no separator in it splits into itself, one component. The
# two laws under it are read off this one.
law split_plain:
  for +p: String
  for +e: {D1.slashless(p) == True{} : Bool}
  {String.split(p, '/') == [p] : List<&2, String>}

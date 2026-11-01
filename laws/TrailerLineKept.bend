import Base
import ../src/ez/gate.bend as G

# LAW: a trailer line is kept with the `#|` dropped
law want_keeps:
  for +rest: String
  for +t: List<&2, String>
  {G.want(("#|" ++ rest) <> t) == rest <> G.want(t) : List<&2, String>}

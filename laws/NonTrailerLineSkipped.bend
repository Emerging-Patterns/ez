import Base
import ../src/ez/gate.bend as G

# trailer: what a test file states its run must print

# LAW: a line that does not open with `#|` is not a trailer line
law want_skips:
  for +h: String
  for +t: List<&2, String>
  for e: {False{} == String.starts_with(h, "#|") : Bool}
  {G.want(h <> t) == G.want(t) : List<&2, String>}

# LAW: so a file whose first line is not a trailer line states the trailer
# its other lines state
law trailer_skips:
  for text: String
  for +h: String
  for t: List<&2, String>
  for e: {h <> t == String.lines(text) : List<&2, String>}
  for ne: {False{} == String.starts_with(h, "#|") : Bool}
  {G.trailer(text) == String.join(G.want(t), "\n") : String}

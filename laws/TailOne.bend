import Base
import ../src/pkg/path.bend as Path

# LAW: the last component of a path is the tail of length one. `base` and
# `tail` are written differently and this holds the one to the other.
law tail_one:
  for +p: String
  {Path.tail(p, 1n) == Path.base(p) : String}

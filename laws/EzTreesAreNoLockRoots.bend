import Base
import ../src/lock/plan.bend as P
import ../src/lock/world.bend as W

# LAW: a tracked path under `.ez/` is never a root of the lock. The trees
# there are packages, read as packages, and not the project's own sources.
law root_skips_ez:
  for +p: String
  for text: String
  {P.roots.one(W.Source{".ez/" ++ p, text}) == [] : List<&2, String>}

# proofs of laws/ClimbedAbsolutePathStaysAbsolute.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/pkg/path.bend as Path
import ../src/add/world.bend as A
import ../laws/ClimbedAbsolutePathStaysAbsolute.bend as Laws
import ../laws/NormKeepsAbsolute.bend as L1
import ./lemmas/LockPlannerFacts.bend as M1

# LAW: one character of the prefix test, with the character's verdict given as
# a parameter. A path that begins at the root begins with the separator, and
# appending to it leaves that character where it was.
law abs_append.arm:
  for +h: Char
  for +t: String
  for +x: String
  for b: Bool
  for eb: {b == Char.is_eq(h, '/') : Bool}
  for e: {True{} == String.starts_with.go.if("", t, b) : Bool}
  {String.starts_with(String.append(SCon{h, t}, x), "/") == True{} : Bool}

def abs_append.arm(h, t, x, b, eb, e):
  match b:
    case True{}:
      %eb : {String.starts_with.go.if("", String.append(t, x), _) == True{} : Bool}
      Eq.starts_nil(String.append(t, x))
    case False{}:
      Eq.bit.absurd2(&2,
        {String.starts_with(String.append(SCon{h, t}, x), "/") == True{}
          : Bool}, e)

# LAW: appending to an absolute path leaves it absolute
law abs_append:
  for +p: String
  for +x: String
  for e: {True{} == String.starts_with(p, "/") : Bool}
  {String.starts_with(String.append(p, x), "/") == True{} : Bool}

def abs_append(p, x, e):
  match p:
    case SNil{}:
      Eq.bit.absurd2(&2,
        {String.starts_with(String.append(SNil{}, x), "/") == True{} : Bool}, e)
    case SCon{+h, +t}:
      abs_append.arm(h, t, x, Char.is_eq(h, '/'), {==}, e)

# By induction on the count. Climbing nothing is normalising, which is the law
# above; climbing once more is normalising the path with a climb spliced onto
# it, and the splice leaves the leading separator alone.
def Laws.climb_absolute(n, p, e):
  match n:
    case 0n:
      L1.norm_absolute(p, e)
    case 1n+q:
      Laws.climb_absolute(q, Path.dir(p),
        Equal.sym(Bool, String.starts_with(Path.dir(p), "/"), True{},
          L1.norm_absolute(String.append(p, "/.."),
            Equal.sym(Bool,
              String.starts_with(String.append(p, "/.."), "/"), True{},
              abs_append(p, "/..", e)))))

# proofs of laws/EqualsInPathNamed.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/plan.bend as P
import ../laws/EqualsInPathNamed.bend as Laws

# LAW: a path that holds `=` is not empty
law eqless_filled:
  for +at: String
  for e: {False{} == P.path.eqless(at) : Bool}
  {False{} == String.is_empty(at) : Bool}

def eqless_filled(at, e):
  match at:
    case SNil{}:
      Eq.bit.absurd(&2, {False{} == String.is_empty(SNil{}) : Bool}, e)
    case SCon{h, t}:
      {==}

# the reason a lock that is not lockable gives, from the scan's answer
def named.why(+why: String) -> String:
  P.lockable.pick(String.is_empty(why), why)

# The first path the scan finds is the one given, and it is not empty, so
# the reason is the one that names it.
def Laws.path_eq_named(hash, _src, at, _sum, fs, rest, e):
  f = eqless_filled(at, e)
  %e : {named.why(P.packs.eq.pick(String.is_empty(P.path.eq.pick(_, at,
    P.path.eq.first(fs))), hash, P.path.eq.pick(_, at, P.path.eq.first(fs)),
    P.packs.eq(rest))) == P.path.eq.why(hash, at) : String}
  %f : {named.why(P.packs.eq.pick(_, hash, at, P.packs.eq(rest)))
    == P.path.eq.why(hash, at) : String}
  {==}

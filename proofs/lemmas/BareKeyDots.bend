# a dot anywhere ends a bare key
import Base
import ../../src/ez/target.bend as Tgt
import ../../src/ez/named.bend as Named

# LAW: a step whose rest is false is false, whatever the char was
law step_false:
  for ok: Bool
  for r: Unit -> Bool
  for e: {r(Unit{}) == False{} : Bool}
  {Named.bare.step(ok, r) == False{} : Bool}

def step_false(ok, _r, e):
  match ok:
    case True{}:
      e
    case False{}:
      {==}

# LAW: past the first char, a dot anywhere ends a bare key
law rest_no_dot:
  for +a: String
  for +b: String
  {Named.bare.rest(a ++ ("." ++ b)) == False{} : Bool}

def rest_no_dot(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      step_false(Tgt.plain.at(h), _u => Named.bare.rest(t ++ ("." ++ b)),
        rest_no_dot(t, b))

# LAW: a dot anywhere ends a bare key
law bare_dot:
  for +a: String
  for +b: String
  {Named.bare(a ++ ("." ++ b)) == False{} : Bool}

def bare_dot(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      step_false(Tgt.plain.at(h), _u => Named.bare.rest(t ++ ("." ++ b)),
        rest_no_dot(t, b))

# proofs of laws/LedgerNamesFirst.bend
import Base
import ../src/check/eq.bend as Eq
import ../src/lock/lock.bend as L
import ../src/lock/world.bend as W
import ../laws/LedgerNamesFirst.bend as Laws

# LAW: one name of a table's front, with whether it is the one looked for
# decided
law nm.find_left.step:
  for +c: Bool
  for +h: String
  for +t: List<&2, L.Name>
  for +ys: List<&2, L.Name>
  for +nv: String
  for +f: {False{} == String.is_empty(L.name.at(c, h, _u => L.name.find(t, nv))) : Bool}
  for ih: {False{} == String.is_empty(L.name.find(t, nv)) : Bool}
    -> {L.name.find(List.append(&2, L.Name, t, ys), nv) == L.name.find(t, nv) : String}
  {L.name.at(c, h, _u => L.name.find(List.append(&2, L.Name, t, ys), nv))
    == L.name.at(c, h, _u => L.name.find(t, nv)) : String}

def nm.find_left.step(c, _h, _t, _ys, _nv, f, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      ih(f)

# LAW: a table's front answers for a name it resolves, whatever follows it
law nm.find_left:
  for +xs: List<&2, L.Name>
  for +ys: List<&2, L.Name>
  for +nv: String
  for +f: {False{} == String.is_empty(L.name.find(xs, nv)) : Bool}
  {L.name.find(List.append(&2, L.Name, xs, ys), nv) == L.name.find(xs, nv) : String}

def nm.find_left(xs, ys, nv, f):
  match xs:
    case []:
      Eq.bit.absurd(&2, {L.name.find(List.append(&2, L.Name, [], ys), nv) == L.name.find([], nv)
        : String}, f)
    case L.Name{+n, +h} <> +t:
      nm.find_left.step(String.eq(n, nv), h, t, ys, nv, f, z => nm.find_left(t, ys, nv, z))

def Laws.ledger_names_first(led, js, nv, f):
  nm.find_left(L.ledger.names(led), W.names.of(js), nv, f)

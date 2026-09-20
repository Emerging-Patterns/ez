# manifest: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./toml.bend as T
import ./manifest.bend as M
import ./render.bend as R
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

def Laws.value_first(k, v, ps):
  Equal.cong(Bool, String, b => Bool.pick(String, b, v, T.value(ps, k)),
    String.eq(k, k), True{}, Eq.string_eq_self(k))

# LAW: one step of the drop, with the branch the pick takes given as a
# parameter and the equation that put it there given alongside, since a match
# may not scrutinise a computed value
law without_idem.arm:
  for -h: M.Dep
  for -r: List<&2, M.Dep>
  for +name: String
  for b: Bool
  for eb: {String.eq(M.dep.name(h), name) == b : Bool}
  for ih: {R.without(r, name) == r : List<&2, M.Dep>}
  {R.without(R.without.put(b, h, r), name) == R.without.put(b, h, r)
    : List<&2, M.Dep>}

def without_idem.arm(h, r, name, b, eb, ih):
  match b:
    case True{}:
      ih
    case False{}:
      Equal.trans(List<&2, M.Dep>,
        R.without.put(String.eq(M.dep.name(h), name), h, R.without(r, name)),
        R.without.put(False{}, h, R.without(r, name)),
        h <> r,
        Equal.cong(Bool, List<&2, M.Dep>,
          x => R.without.put(x, h, R.without(r, name)),
          String.eq(M.dep.name(h), name), False{}, eb),
        Equal.cong(List<&2, M.Dep>, List<&2, M.Dep>, y => h <> y,
          R.without(r, name), r, ih))

def Laws.without_idem(ds, name):
  match ds:
    case []:
      {==}
    case +h <> t:
      without_idem.arm(h, R.without(t, name), name,
        String.eq(M.dep.name(h), name), {==}, Laws.without_idem(t, name))

# LAW: a dependency appended to a list the drop already cleaned is dropped
# again by the same name
law without_append:
  for xs: List<&2, M.Dep>
  for +d: M.Dep
  {R.without(List.append(&2, M.Dep, xs, [d]), M.dep.name(d))
    == R.without(xs, M.dep.name(d)) : List<&2, M.Dep>}

def without_append(xs, d):
  match xs:
    case []:
      Equal.cong(Bool, List<&2, M.Dep>,
        b => R.without.put(b, d, []), String.eq(M.dep.name(d), M.dep.name(d)),
        True{}, Eq.string_eq_self(M.dep.name(d)))
    case +h <> t:
      Equal.cong(List<&2, M.Dep>, List<&2, M.Dep>,
        y => R.without.put(String.eq(M.dep.name(h), M.dep.name(d)), h, y),
        R.without(List.append(&2, M.Dep, t, [d]), M.dep.name(d)),
        R.without(t, M.dep.name(d)),
        without_append(t, d))

def Laws.add_idem(m, d):
  match m:
    case M.Manifest{+n, +e, +ds}:
      Equal.cong(List<&2, M.Dep>, M.Manifest,
        y => M.Manifest{n, e, List.append(&2, M.Dep, y, [d])},
        R.without(List.append(&2, M.Dep, R.without(ds, M.dep.name(d)), [d]),
          M.dep.name(d)),
        R.without(ds, M.dep.name(d)),
        Equal.trans(List<&2, M.Dep>,
          R.without(List.append(&2, M.Dep, R.without(ds, M.dep.name(d)), [d]),
            M.dep.name(d)),
          R.without(R.without(ds, M.dep.name(d)), M.dep.name(d)),
          R.without(ds, M.dep.name(d)),
          without_append(R.without(ds, M.dep.name(d)), d),
          Laws.without_idem(ds, M.dep.name(d))))

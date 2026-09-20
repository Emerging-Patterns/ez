# lock: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./lock.bend as L
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

def Laws.origin_first(h, s, rest):
  Equal.cong(Bool, L.Src, b => Bool.pick(L.Src, b, s, L.origin(rest, h)),
    String.eq(h, h), True{}, Eq.string_eq_self(h))

# LAW: a hash recorded at the head of a list of origins resolves to what was
# recorded for it, whatever the list behind it holds. This is `origin_first`
# again, and it is stated here because the agreement law needs it at two
# different tails: the cache on one side, nothing at all on the other.
law head_wins:
  for +h: String
  for s: L.Src
  for rest: List<&2, L.Origin>
  {L.origin(L.Origin{h, s} <> rest, h) == s : L.Src}

def head_wins(h, s, rest):
  Equal.cong(Bool, L.Src, b => Bool.pick(L.Src, b, s, L.origin(rest, h)),
    String.eq(h, h), True{}, Eq.string_eq_self(h))

def Laws.origin_agrees(h, s, cache):
  Equal.trans(L.Src,
    L.origin(L.origins.all([L.Origin{h, s}], cache), h),
    s,
    L.origin(L.origins.all([], [L.Origin{h, s}]), h),
    head_wins(h, s, cache),
    Equal.sym(L.Src, L.origin(L.origins.all([], [L.Origin{h, s}]), h), s,
      head_wins(h, s, [])))

# LAW: one step of the scan, with the head's answer given as a parameter,
# since a match may not scrutinise a computed value, and the rest of the
# scan's agreement given alongside
law seen_holds_agrees.arm:
  for t: List<&2, String>
  for +s: String
  for p: Bool
  for ih: {Laws.old.seen.holds(t, s) == L.seen.holds(t, s) : Bool}
  {Bool.or(p, Laws.old.seen.holds(t, s))
    == L.any.step(p, _u => L.seen.holds(t, s)) : Bool}

def seen_holds_agrees.arm(_t, _s, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.seen_holds_agrees(xs, s):
  match xs:
    case []:
      {==}
    case +h <> +t:
      seen_holds_agrees.arm(t, s, String.eq(h, s), Laws.seen_holds_agrees(t, s))

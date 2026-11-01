# inserting files in path order: the swap, and the order being total
#
# The long half of this file is the order-independence of `manifest_of`:
# that a package renders the same manifest, and so is published under the
# same `0x` name, whatever order its files were found in. It was out of
# reach while the sort was Base's `List.sort`; it is reachable now that it
# is this project's own `file.sort`, and what it wanted was a permutation
# lemma over `file.ins`. That lemma needs the order files are sorted by to
# be a total order — one way round or the other, never both, and transitive
# — which is a fact about Base's `String.is_le` that Base does not state, so
# the walk down to `Word.cmp` is proved here too. `tests/publish.sh` still
# pins ez's answer against a real `bend --publish`; it is no longer the only
# thing holding this end down.
import Base
import ../../src/check/eq.bend as Eq
import ../../src/pkg/pkg.bend as K
import ../../src/pub/blurb.bend as B
import ../../src/add/world.bend as A
import ../../laws/ManifestIgnoresFileOrder.bend as L1
import ../../laws/SortIgnoresFileOrder.bend as L2
import ../../laws/defs/LockInputs.bend as D1
import ./LockPlannerFacts.bend as M1
import ./RenderedLedgerRows.bend as M2

# LAW: a comparison that is at most EQ on two sides is at most EQ across
law le.trans.go:
  for u: Cmp
  for v: Cmp
  for w: Cmp
  for ok: {M1.tri(u, v, w) == True{} : Bool}
  for eu: {Cmp.is_le(u) == True{} : Bool}
  for ev: {Cmp.is_le(v) == True{} : Bool}
  {Cmp.is_le(w) == True{} : Bool}

def le.trans.go(u, v, w, ok, eu, ev):
  match u v:
    case LT{} LT{}:
      match w:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          ok
    case LT{} EQ{}:
      match w:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          ok
    case EQ{} LT{}:
      match w:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          ok
    case EQ{} EQ{}:
      match w:
        case LT{}:
          {==}
        case EQ{}:
          {==}
        case GT{}:
          ok
    case LT{} GT{}:
      Eq.bit.absurd(&2, {Cmp.is_le(w) == True{} : Bool}, ev)
    case EQ{} GT{}:
      Eq.bit.absurd(&2, {Cmp.is_le(w) == True{} : Bool}, ev)
    case GT{} _:
      Eq.bit.absurd(&2, {Cmp.is_le(w) == True{} : Bool}, eu)

# LAW: the order files are written in is transitive, as a total order is
law le.trans:
  for +x: K.Item
  for +y: K.Item
  for +z: K.Item
  for exy: {K.file.le(x, y) == True{} : Bool}
  for eyz: {K.file.le(y, z) == True{} : Bool}
  {K.file.le(x, z) == True{} : Bool}

def le.trans(x, y, z, exy, eyz):
  le.trans.go(
    String.order(K.file.at(x), K.file.at(y)),
    String.order(K.file.at(y), K.file.at(z)),
    String.order(K.file.at(x), K.file.at(z)),
    M1.str.tri(K.file.at(x), K.file.at(y), K.file.at(z)),
    exy, eyz)

law eq.is.order:
  for +a: String
  for +b: String
  {String.eq(a, b) == Cmp.is_eq(String.order(a, b)) : Bool}

# Base's String.eq is that comparison read as a bit
def eq.is.order(_a, _b):
  {==}

# LAW: of two comparisons that are not a tie, exactly one is at most EQ
law le.excl.go:
  for u: Cmp
  for eu: {Cmp.is_eq(u) == False{} : Bool}
  {Cmp.is_le(u) == Bool.not(Cmp.is_le(M1.cmp.flip(u))) : Bool}

def le.excl.go(u, eu):
  match u:
    case LT{}:
      {==}
    case EQ{}:
      Eq.bit.absurd2(&2,
        {Cmp.is_le(EQ{}) == Bool.not(Cmp.is_le(M1.cmp.flip(EQ{}))) : Bool}, eu)
    case GT{}:
      {==}

# LAW: two files with different paths sit one way round or the other, never
# both and never neither. This is what the order of a package's files rests
# on: a package holds each path once, so no two of its files tie.
law le.excl:
  for +a: K.Item
  for +b: K.Item
  for ne: {String.eq(K.file.at(a), K.file.at(b)) == False{} : Bool}
  {K.file.le(a, b) == Bool.not(K.file.le(b, a)) : Bool}

def le.excl(a, b, ne):
  Equal.trans(Bool,
    Cmp.is_le(String.order(K.file.at(a), K.file.at(b))),
    Bool.not(Cmp.is_le(M1.cmp.flip(String.order(K.file.at(a), K.file.at(b))))),
    Bool.not(Cmp.is_le(String.order(K.file.at(b), K.file.at(a)))),
    le.excl.go(String.order(K.file.at(a), K.file.at(b)),
      Equal.trans(Bool,
        Cmp.is_eq(String.order(K.file.at(a), K.file.at(b))),
        String.eq(K.file.at(a), K.file.at(b)),
        False{},
        Equal.sym(Bool, String.eq(K.file.at(a), K.file.at(b)),
          Cmp.is_eq(String.order(K.file.at(a), K.file.at(b))),
          eq.is.order(K.file.at(a), K.file.at(b))),
        ne)),
    Equal.cong(Cmp, Bool, w => Bool.not(Cmp.is_le(w)),
      M1.cmp.flip(String.order(K.file.at(a), K.file.at(b))),
      String.order(K.file.at(b), K.file.at(a)),
      Equal.sym(Cmp, String.order(K.file.at(b), K.file.at(a)),
        M1.cmp.flip(String.order(K.file.at(a), K.file.at(b))),
        M1.str.flip(K.file.at(a), K.file.at(b)))))

# LAW: two files inserted into an empty list in either order land the same way
law ins.swap.nil:
  for +a: K.Item
  for +b: K.Item
  for ba: Bool
  for eba: {K.file.le(b, a) == ba : Bool}
  for eab: {K.file.le(a, b) == Bool.not(ba) : Bool}
  {K.file.ins(K.file.ins([], a), b) == K.file.ins(K.file.ins([], b), a)
    : List<&2, K.Item>}

def ins.swap.nil(a, b, ba, eba, eab):
  match ba:
    case True{}:
      Equal.trans(List<&2, K.Item>,
        K.file.ins(K.file.ins([], a), b),
        b <> (a <> []),
        K.file.ins(K.file.ins([], b), a),
        Equal.cong(Bool, List<&2, K.Item>,
          y => K.file.ins.put(y, b, a, [], [b]),
          K.file.le(b, a), True{}, eba),
        Equal.sym(List<&2, K.Item>,
          K.file.ins(K.file.ins([], b), a), b <> (a <> []),
          Equal.cong(Bool, List<&2, K.Item>,
            y => K.file.ins.put(y, a, b, [], [a]),
            K.file.le(a, b), False{}, eab)))
    case False{}:
      Equal.trans(List<&2, K.Item>,
        K.file.ins(K.file.ins([], a), b),
        a <> (b <> []),
        K.file.ins(K.file.ins([], b), a),
        Equal.cong(Bool, List<&2, K.Item>,
          y => K.file.ins.put(y, b, a, [], [b]),
          K.file.le(b, a), False{}, eba),
        Equal.sym(List<&2, K.Item>,
          K.file.ins(K.file.ins([], b), a), a <> (b <> []),
          Equal.cong(Bool, List<&2, K.Item>,
            y => K.file.ins.put(y, a, b, [], [a]),
            K.file.le(a, b), True{}, eab)))

# LAW: both files belong before the head, so both end up in front of it, in
# the order their own comparison puts them
law ins.swap.tt:
  for +h: K.Item
  for +t: List<&2, K.Item>
  for +a: K.Item
  for +b: K.Item
  for ba: Bool
  for eba: {K.file.le(b, a) == ba : Bool}
  for eab: {K.file.le(a, b) == Bool.not(ba) : Bool}
  for eA: {K.file.le(a, h) == True{} : Bool}
  for eB: {K.file.le(b, h) == True{} : Bool}
  {K.file.ins(K.file.ins.put(True{}, a, h, t, K.file.ins(t, a)), b)
    == K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a)
    : List<&2, K.Item>}

def ins.swap.tt(h, t, a, b, ba, eba, eab, eA, eB):
  match ba:
    case True{}:
      Equal.trans(List<&2, K.Item>,
        K.file.ins(K.file.ins.put(True{}, a, h, t, K.file.ins(t, a)), b),
        b <> (a <> (h <> t)),
        K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a),
        Equal.trans(List<&2, K.Item>,
          K.file.ins(K.file.ins.put(True{}, a, h, t, K.file.ins(t, a)), b),
          K.file.ins.put(K.file.le(b, a), b, a, h <> t, b <> (h <> t)),
          b <> (a <> (h <> t)),
          Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
            r => K.file.ins.put(K.file.le(b, a), b, a, h <> t, r),
            K.file.ins(h <> t, b), b <> (h <> t),
            Equal.cong(Bool, List<&2, K.Item>,
              y => K.file.ins.put(y, b, h, t, K.file.ins(t, b)),
              K.file.le(b, h), True{}, eB)),
          Equal.cong(Bool, List<&2, K.Item>,
            y => K.file.ins.put(y, b, a, h <> t, b <> (h <> t)),
            K.file.le(b, a), True{}, eba)),
        Equal.sym(List<&2, K.Item>,
          K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a),
          b <> (a <> (h <> t)),
          Equal.trans(List<&2, K.Item>,
            K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a),
            K.file.ins.put(K.file.le(a, b), a, b, h <> t, a <> (h <> t)),
            b <> (a <> (h <> t)),
            Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
              r => K.file.ins.put(K.file.le(a, b), a, b, h <> t, r),
              K.file.ins(h <> t, a), a <> (h <> t),
              Equal.cong(Bool, List<&2, K.Item>,
                y => K.file.ins.put(y, a, h, t, K.file.ins(t, a)),
                K.file.le(a, h), True{}, eA)),
            Equal.cong(Bool, List<&2, K.Item>,
              y => K.file.ins.put(y, a, b, h <> t, a <> (h <> t)),
              K.file.le(a, b), False{}, eab))))
    case False{}:
      Equal.trans(List<&2, K.Item>,
        K.file.ins(K.file.ins.put(True{}, a, h, t, K.file.ins(t, a)), b),
        a <> (b <> (h <> t)),
        K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a),
        Equal.trans(List<&2, K.Item>,
          K.file.ins(K.file.ins.put(True{}, a, h, t, K.file.ins(t, a)), b),
          K.file.ins.put(K.file.le(b, a), b, a, h <> t, b <> (h <> t)),
          a <> (b <> (h <> t)),
          Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
            r => K.file.ins.put(K.file.le(b, a), b, a, h <> t, r),
            K.file.ins(h <> t, b), b <> (h <> t),
            Equal.cong(Bool, List<&2, K.Item>,
              y => K.file.ins.put(y, b, h, t, K.file.ins(t, b)),
              K.file.le(b, h), True{}, eB)),
          Equal.cong(Bool, List<&2, K.Item>,
            y => K.file.ins.put(y, b, a, h <> t, b <> (h <> t)),
            K.file.le(b, a), False{}, eba)),
        Equal.sym(List<&2, K.Item>,
          K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a),
          a <> (b <> (h <> t)),
          Equal.trans(List<&2, K.Item>,
            K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a),
            K.file.ins.put(K.file.le(a, b), a, b, h <> t, a <> (h <> t)),
            a <> (b <> (h <> t)),
            Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
              r => K.file.ins.put(K.file.le(a, b), a, b, h <> t, r),
              K.file.ins(h <> t, a), a <> (h <> t),
              Equal.cong(Bool, List<&2, K.Item>,
                y => K.file.ins.put(y, a, h, t, K.file.ins(t, a)),
                K.file.le(a, h), True{}, eA)),
            Equal.cong(Bool, List<&2, K.Item>,
              y => K.file.ins.put(y, a, b, h <> t, a <> (h <> t)),
              K.file.le(a, b), True{}, eab))))

# LAW: the first file belongs before the head and the second does not, so the
# second stays behind it and the first goes in front, whichever way round the
# two were offered. A file that came before the first would come before the
# head too, so the branch where one does is no branch at all.
law ins.swap.tf:
  for +h: K.Item
  for +t: List<&2, K.Item>
  for +a: K.Item
  for +b: K.Item
  for ba: Bool
  for eba: {K.file.le(b, a) == ba : Bool}
  for eA: {K.file.le(a, h) == True{} : Bool}
  for eB: {K.file.le(b, h) == False{} : Bool}
  {K.file.ins(K.file.ins.put(True{}, a, h, t, K.file.ins(t, a)), b)
    == K.file.ins(K.file.ins.put(False{}, b, h, t, K.file.ins(t, b)), a)
    : List<&2, K.Item>}

def ins.swap.tf(h, t, a, b, ba, eba, eA, eB):
  match ba:
    case True{}:
      Eq.bit.absurd2(&2,
        {K.file.ins(K.file.ins.put(True{}, a, h, t, K.file.ins(t, a)), b)
          == K.file.ins(K.file.ins.put(False{}, b, h, t, K.file.ins(t, b)), a)
          : List<&2, K.Item>},
        Equal.trans(Bool, True{}, K.file.le(b, h), False{},
          Equal.sym(Bool, K.file.le(b, h), True{},
            le.trans(b, a, h, eba, eA)),
          eB))
    case False{}:
      Equal.trans(List<&2, K.Item>,
        K.file.ins(K.file.ins.put(True{}, a, h, t, K.file.ins(t, a)), b),
        a <> (h <> K.file.ins(t, b)),
        K.file.ins(K.file.ins.put(False{}, b, h, t, K.file.ins(t, b)), a),
        Equal.trans(List<&2, K.Item>,
          K.file.ins(K.file.ins.put(True{}, a, h, t, K.file.ins(t, a)), b),
          K.file.ins.put(K.file.le(b, a), b, a, h <> t, h <> K.file.ins(t, b)),
          a <> (h <> K.file.ins(t, b)),
          Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
            r => K.file.ins.put(K.file.le(b, a), b, a, h <> t, r),
            K.file.ins(h <> t, b), h <> K.file.ins(t, b),
            Equal.cong(Bool, List<&2, K.Item>,
              y => K.file.ins.put(y, b, h, t, K.file.ins(t, b)),
              K.file.le(b, h), False{}, eB)),
          Equal.cong(Bool, List<&2, K.Item>,
            y => K.file.ins.put(y, b, a, h <> t, h <> K.file.ins(t, b)),
            K.file.le(b, a), False{}, eba)),
        Equal.sym(List<&2, K.Item>,
          K.file.ins(K.file.ins.put(False{}, b, h, t, K.file.ins(t, b)), a),
          a <> (h <> K.file.ins(t, b)),
          Equal.cong(Bool, List<&2, K.Item>,
            y => K.file.ins.put(y, a, h, K.file.ins(t, b),
              K.file.ins(K.file.ins(t, b), a)),
            K.file.le(a, h), True{}, eA)))

# LAW: the mirror of the one above, with the two files the other way round
law ins.swap.ft:
  for +h: K.Item
  for +t: List<&2, K.Item>
  for +a: K.Item
  for +b: K.Item
  for ab: Bool
  for eab: {K.file.le(a, b) == ab : Bool}
  for eA: {K.file.le(a, h) == False{} : Bool}
  for eB: {K.file.le(b, h) == True{} : Bool}
  {K.file.ins(K.file.ins.put(False{}, a, h, t, K.file.ins(t, a)), b)
    == K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a)
    : List<&2, K.Item>}

def ins.swap.ft(h, t, a, b, ab, eab, eA, eB):
  match ab:
    case True{}:
      Eq.bit.absurd2(&2,
        {K.file.ins(K.file.ins.put(False{}, a, h, t, K.file.ins(t, a)), b)
          == K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a)
          : List<&2, K.Item>},
        Equal.trans(Bool, True{}, K.file.le(a, h), False{},
          Equal.sym(Bool, K.file.le(a, h), True{},
            le.trans(a, b, h, eab, eB)),
          eA))
    case False{}:
      Equal.trans(List<&2, K.Item>,
        K.file.ins(K.file.ins.put(False{}, a, h, t, K.file.ins(t, a)), b),
        b <> (h <> K.file.ins(t, a)),
        K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a),
        Equal.cong(Bool, List<&2, K.Item>,
          y => K.file.ins.put(y, b, h, K.file.ins(t, a),
            K.file.ins(K.file.ins(t, a), b)),
          K.file.le(b, h), True{}, eB),
        Equal.sym(List<&2, K.Item>,
          K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a),
          b <> (h <> K.file.ins(t, a)),
          Equal.trans(List<&2, K.Item>,
            K.file.ins(K.file.ins.put(True{}, b, h, t, K.file.ins(t, b)), a),
            K.file.ins.put(K.file.le(a, b), a, b, h <> t,
              h <> K.file.ins(t, a)),
            b <> (h <> K.file.ins(t, a)),
            Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
              r => K.file.ins.put(K.file.le(a, b), a, b, h <> t, r),
              K.file.ins(h <> t, a), h <> K.file.ins(t, a),
              Equal.cong(Bool, List<&2, K.Item>,
                y => K.file.ins.put(y, a, h, t, K.file.ins(t, a)),
                K.file.le(a, h), False{}, eA)),
            Equal.cong(Bool, List<&2, K.Item>,
              y => K.file.ins.put(y, a, b, h <> t, h <> K.file.ins(t, a)),
              K.file.le(a, b), False{}, eab))))

# LAW: neither file belongs before the head, so both go past it and the swap
# is the one the shorter list already answered for
law ins.swap.ff:
  for +h: K.Item
  for +t: List<&2, K.Item>
  for +a: K.Item
  for +b: K.Item
  for eA: {K.file.le(a, h) == False{} : Bool}
  for eB: {K.file.le(b, h) == False{} : Bool}
  for ih: {K.file.ins(K.file.ins(t, a), b) == K.file.ins(K.file.ins(t, b), a)
    : List<&2, K.Item>}
  {K.file.ins(K.file.ins.put(False{}, a, h, t, K.file.ins(t, a)), b)
    == K.file.ins(K.file.ins.put(False{}, b, h, t, K.file.ins(t, b)), a)
    : List<&2, K.Item>}

def ins.swap.ff(h, t, a, b, eA, eB, ih):
  Equal.trans(List<&2, K.Item>,
    K.file.ins(K.file.ins.put(False{}, a, h, t, K.file.ins(t, a)), b),
    h <> K.file.ins(K.file.ins(t, a), b),
    K.file.ins(K.file.ins.put(False{}, b, h, t, K.file.ins(t, b)), a),
    Equal.cong(Bool, List<&2, K.Item>,
      y => K.file.ins.put(y, b, h, K.file.ins(t, a),
        K.file.ins(K.file.ins(t, a), b)),
      K.file.le(b, h), False{}, eB),
    Equal.trans(List<&2, K.Item>,
      h <> K.file.ins(K.file.ins(t, a), b),
      h <> K.file.ins(K.file.ins(t, b), a),
      K.file.ins(K.file.ins.put(False{}, b, h, t, K.file.ins(t, b)), a),
      Equal.cong(List<&2, K.Item>, List<&2, K.Item>, r => h <> r,
        K.file.ins(K.file.ins(t, a), b), K.file.ins(K.file.ins(t, b), a), ih),
      Equal.sym(List<&2, K.Item>,
        K.file.ins(K.file.ins.put(False{}, b, h, t, K.file.ins(t, b)), a),
        h <> K.file.ins(K.file.ins(t, b), a),
        Equal.cong(Bool, List<&2, K.Item>,
          y => K.file.ins.put(y, a, h, K.file.ins(t, b),
            K.file.ins(K.file.ins(t, b), a)),
          K.file.le(a, h), False{}, eA))))

# LAW: one step of the swap, with the two comparisons against the head given
# as parameters and the equations that put them there given alongside
law ins.swap.arm:
  for +h: K.Item
  for +t: List<&2, K.Item>
  for +a: K.Item
  for +b: K.Item
  for A: Bool
  for eA: {K.file.le(a, h) == A : Bool}
  for M2.B: Bool
  for eB: {K.file.le(b, h) == M2.B : Bool}
  for exc: {K.file.le(a, b) == Bool.not(K.file.le(b, a)) : Bool}
  for ih: {K.file.ins(K.file.ins(t, a), b) == K.file.ins(K.file.ins(t, b), a)
    : List<&2, K.Item>}
  {K.file.ins(K.file.ins.put(A, a, h, t, K.file.ins(t, a)), b)
    == K.file.ins(K.file.ins.put(M2.B, b, h, t, K.file.ins(t, b)), a)
    : List<&2, K.Item>}

def ins.swap.arm(h, t, a, b, A, eA, M2.B, eB, exc, ih):
  match A M2.B:
    case True{} True{}:
      ins.swap.tt(h, t, a, b, K.file.le(b, a), {==}, exc, eA, eB)
    case True{} False{}:
      ins.swap.tf(h, t, a, b, K.file.le(b, a), {==}, eA, eB)
    case False{} True{}:
      ins.swap.ft(h, t, a, b, K.file.le(a, b), {==}, eA, eB)
    case False{} False{}:
      ins.swap.ff(h, t, a, b, eA, eB, ih)

# LAW: two files with different paths inserted into a list in either order
# give the same list. The list is any list: the sort's accumulator is in order
# already, but the induction never needs to say so.
law ins.swap:
  for xs: List<&2, K.Item>
  for +a: K.Item
  for +b: K.Item
  for +ne: {String.eq(K.file.at(a), K.file.at(b)) == False{} : Bool}
  {K.file.ins(K.file.ins(xs, a), b) == K.file.ins(K.file.ins(xs, b), a)
    : List<&2, K.Item>}

def ins.swap(xs, a, b, ne):
  match xs:
    case []:
      ins.swap.nil(a, b, K.file.le(b, a), {==}, le.excl(a, b, ne))
    case Con{+h, +t}:
      ins.swap.arm(h, t, a, b, K.file.le(a, h), {==}, K.file.le(b, h), {==},
        le.excl(a, b, ne), ins.swap(t, a, b, ne))

# LAW: a path that is none of a list's paths is none of the paths of that
# list with one more file put in it, as long as it is not that file's either
law fresh.ins_at:
  for +n: Nat
  for +x: K.Item
  for +y: K.Item
  for +xs: List<&2, K.Item>
  for nxy: {String.eq(K.file.at(x), K.file.at(y)) == False{} : Bool}
  for +fx: {D1.file.fresh(x, xs) == True{} : Bool}
  {D1.file.fresh(x, D1.files.perm.ins_at(n, y, xs)) == True{} : Bool}

def fresh.ins_at(n, x, y, xs, nxy, fx):
  match n xs:
    case 0n _:
      Equal.trans(Bool,
        D1.file.fresh(x, y <> xs),
        D1.file.fresh(x, xs),
        True{},
        Equal.cong(Bool, Bool,
          u => Bool.and(Bool.not(u), D1.file.fresh(x, xs)),
          String.eq(K.file.at(x), K.file.at(y)), False{}, nxy),
        fx)
    case 1n+p Nil{}:
      Equal.cong(Bool, Bool, u => Bool.and(Bool.not(u), True{}),
        String.eq(K.file.at(x), K.file.at(y)), False{}, nxy)
    case 1n+p Con{+h, +t}:
      Equal.trans(Bool,
        D1.file.fresh(x, h <> D1.files.perm.ins_at(p, y, t)),
        Bool.and(Bool.not(String.eq(K.file.at(x), K.file.at(h))), True{}),
        True{},
        Equal.cong(Bool, Bool,
          v => Bool.and(Bool.not(String.eq(K.file.at(x), K.file.at(h))), v),
          D1.file.fresh(x, D1.files.perm.ins_at(p, y, t)), True{},
          fresh.ins_at(p, x, y, t, nxy,
            Eq.and.right(Bool.not(String.eq(K.file.at(x), K.file.at(h))),
              D1.file.fresh(x, t), fx))),
        Equal.cong(Bool, Bool, u => Bool.and(u, True{}),
          Bool.not(String.eq(K.file.at(x), K.file.at(h))), True{},
          Eq.and.left(Bool.not(String.eq(K.file.at(x), K.file.at(h))),
            D1.file.fresh(x, t), fx)))

# LAW: rearranging a list does not put a path in it that was not there
law fresh.perm:
  for +x: K.Item
  for +ns: List<&2, Nat>
  for +xs: List<&2, K.Item>
  for +fx: {D1.file.fresh(x, xs) == True{} : Bool}
  {D1.file.fresh(x, D1.files.perm(ns, xs)) == True{} : Bool}

def fresh.perm(x, ns, xs, fx):
  match ns xs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{h, t}:
      fx
    case Con{n, ms} Nil{}:
      {==}
    case Con{+n, +ms} Con{+h, +t}:
      fresh.ins_at(n, x, h, D1.files.perm(ms, t),
        Eq.not.true(String.eq(K.file.at(x), K.file.at(h)),
          Eq.and.left(Bool.not(String.eq(K.file.at(x), K.file.at(h))),
            D1.file.fresh(x, t), fx)),
        fresh.perm(x, ms, t,
          Eq.and.right(Bool.not(String.eq(K.file.at(x), K.file.at(h))),
            D1.file.fresh(x, t), fx)))

# LAW: sorting a list with one more file put anywhere in it is sorting the
# list and inserting that file. Where the file was put makes no difference,
# which is the whole of the order-independence, said one file at a time.
law sort.ins_at:
  for +n: Nat
  for +x: K.Item
  for +xs: List<&2, K.Item>
  for +fr: {D1.file.fresh(x, xs) == True{} : Bool}
  {K.file.sort(D1.files.perm.ins_at(n, x, xs)) == K.file.ins(K.file.sort(xs), x)
    : List<&2, K.Item>}

def sort.ins_at(n, x, xs, fr):
  match n xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+h, +t}:
      Equal.trans(List<&2, K.Item>,
        K.file.sort(h <> D1.files.perm.ins_at(p, x, t)),
        K.file.ins(K.file.ins(K.file.sort(t), x), h),
        K.file.ins(K.file.ins(K.file.sort(t), h), x),
        Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
          r => K.file.ins(r, h),
          K.file.sort(D1.files.perm.ins_at(p, x, t)),
          K.file.ins(K.file.sort(t), x),
          sort.ins_at(p, x, t,
            Eq.and.right(Bool.not(String.eq(K.file.at(x), K.file.at(h))),
              D1.file.fresh(x, t), fr))),
        ins.swap(K.file.sort(t), x, h,
          Eq.not.true(String.eq(K.file.at(x), K.file.at(h)),
            Eq.and.left(Bool.not(String.eq(K.file.at(x), K.file.at(h))),
              D1.file.fresh(x, t), fr))))

def L2.sort_perm(ns, xs, dis):
  match ns xs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{h, t}:
      {==}
    case Con{n, ms} Nil{}:
      {==}
    case Con{+n, +ms} Con{+h, +t}:
      Equal.trans(List<&2, K.Item>,
        K.file.sort(D1.files.perm.ins_at(n, h, D1.files.perm(ms, t))),
        K.file.ins(K.file.sort(D1.files.perm(ms, t)), h),
        K.file.ins(K.file.sort(t), h),
        sort.ins_at(n, h, D1.files.perm(ms, t),
          fresh.perm(h, ms, t,
            Eq.and.left(D1.file.fresh(h, t), D1.files.distinct(t), dis))),
        Equal.cong(List<&2, K.Item>, List<&2, K.Item>,
          r => K.file.ins(r, h),
          K.file.sort(D1.files.perm(ms, t)), K.file.sort(t),
          L2.sort_perm(ms, t,
            Eq.and.right(D1.file.fresh(h, t), D1.files.distinct(t), dis))))

def L1.manifest_perm(ns, xs, dis):
  Equal.cong(List<&2, K.Item>, String,
    ys => K.manifest.lines(K.dedup(ys)),
    K.file.sort(D1.files.perm(ns, xs)), K.file.sort(xs),
    L2.sort_perm(ns, xs, dis))

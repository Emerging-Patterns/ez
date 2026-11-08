# facts about the lock, upgrade and command planners that many proofs share:
# pins, answers, walks, order and plans
import Base
import ../../src/check/eq.bend as Eq
import ../../src/check/str.bend as Str
import ../../src/lock/plan.bend as P
import ../../src/pkg/pkg.bend as K
import ../../src/pkg/path.bend as Path
import ../../src/ledger/manifest.bend as M
import ../../src/ledger/render.bend as Rend
import ../../src/ledger/ignore.bend as I
import ../../src/ledger/upgrade.bend as U
import ../../src/pub/world.bend as PW
import ../../src/pub/plan.bend as PP
import ../../src/git/git.bend as Git
import ../../src/lock/lock.bend as L
import ../../src/lock/world.bend as W
import ../../src/lock/up.bend as Up
import ../../src/add/world.bend as A
import ../../src/add/plan.bend as AP
import ../../src/add/hub.bend as H
import ../../src/tool/world.bend as TW
import ../../src/tool/plan.bend as TP
import ../../laws/LedgerAddIdempotent.bend as L1
import ../../laws/PlainComponentKept.bend as L2
import ../../laws/NormKeepsAbsolute.bend as L3
import ../../laws/PublishNeedsDepsOnHub.bend as L4
import ../../laws/ToolCacheReused.bend as L5
import ../../laws/ToolRunExitsWithProgram.bend as L6
import ../../laws/NormKeepsRootFlag.bend as L7
import ../../laws/WalkPinsLedgerSources.bend as L8
import ../../laws/LedgerRemoveIdempotent.bend as L9
import ../../laws/defs/LockInputs.bend as D1
import ../../laws/defs/WorldAfterLock.bend as D2
import ./PlanEffectFacts.bend as M1

# The order-independence of `manifest_of` begins here. The road is: the
# comparison files are sorted by is a total order (down to `Word.cmp`, since
# Base states none of it); therefore two files with different paths inserted
# into a list either way round land the same; therefore sorting a list is
# sorting any rearrangement of it; therefore the manifest, and the `0x` name
# over it, are the walk's answer and not the file system's.

# the comparison taken the other way round
def cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# whether a third comparison is one the first two leave room for
def tri(x: Cmp, y: Cmp, z: Cmp) -> Bool:
  match x y:
    case LT{} LT{}:
      Cmp.is_lt(z)
    case LT{} EQ{}:
      Cmp.is_lt(z)
    case EQ{} LT{}:
      Cmp.is_lt(z)
    case EQ{} EQ{}:
      Cmp.is_eq(z)
    case _ _:
      True{}

# LAW: comparing two bits the other way round flips the answer
law bool.flip:
  for +x: Bool
  for +y: Bool
  {Bool.cmp(y, x) == cmp.flip(Bool.cmp(x, y)) : Cmp}

def bool.flip(x, y):
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

# LAW: three bits compare consistently
law bool.tri:
  for +x: Bool
  for +y: Bool
  for +z: Bool
  {tri(Bool.cmp(x, y), Bool.cmp(y, z), Bool.cmp(x, z)) == True{} : Bool}

def bool.tri(x, y, z):
  match x y z:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

# LAW: one step of a word comparison, taken the other way round
law fin.flip:
  for +x: Bool
  for +y: Bool
  for c: Cmp
  {Word.cmp.fin(y, x, cmp.flip(c)) == cmp.flip(Word.cmp.fin(x, y, c)) : Cmp}

def fin.flip(x, y, c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      bool.flip(x, y)
    case GT{}:
      {==}

# LAW: comparing two words the other way round flips the answer
law word.flip:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, b, a) == cmp.flip(Word.cmp(n, a, b)) : Cmp}

def word.flip(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          Equal.trans(Cmp,
            Word.cmp.fin(bb, ab, Word.cmp(p, bt, at)),
            Word.cmp.fin(bb, ab, cmp.flip(Word.cmp(p, at, bt))),
            cmp.flip(Word.cmp.fin(ab, bb, Word.cmp(p, at, bt))),
            Equal.cong(Cmp, Cmp, r => Word.cmp.fin(bb, ab, r),
              Word.cmp(p, bt, at), cmp.flip(Word.cmp(p, at, bt)),
              word.flip(p, at, bt)),
            fin.flip(ab, bb, Word.cmp(p, at, bt)))

# LAW: a comparison that answers LT at both ends leaves the middle free
law tri.lt.free:
  for y: Cmp
  {tri(LT{}, y, LT{}) == True{} : Bool}

def tri.lt.free(y):
  match y:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# LAW: a comparison that answers LT on the right leaves the first free
law tri.free.lt:
  for x: Cmp
  {tri(x, LT{}, LT{}) == True{} : Bool}

def tri.free.lt(x):
  match x:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# LAW: a GT in the middle constrains nothing
law tri.mid.gt:
  for x: Cmp
  for z: Cmp
  {tri(x, GT{}, z) == True{} : Bool}

def tri.mid.gt(x, _z):
  match x:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# LAW: one step of three word comparisons stays consistent
law fin.tri:
  for +ab: Bool
  for +bb: Bool
  for +cb: Bool
  for x: Cmp
  for y: Cmp
  for z: Cmp
  for ok: {tri(x, y, z) == True{} : Bool}
  {tri(Word.cmp.fin(ab, bb, x), Word.cmp.fin(bb, cb, y),
    Word.cmp.fin(ab, cb, z)) == True{} : Bool}

def fin.tri(ab, bb, cb, x, y, z, ok):
  match x y:
    case LT{} LT{}:
      match z:
        case LT{}:
          {==}
        case EQ{}:
          Eq.bit.absurd(&2, {Cmp.is_lt(Bool.cmp(ab, cb)) == True{} : Bool}, ok)
        case GT{}:
          ok
    case LT{} EQ{}:
      match z:
        case LT{}:
          tri.lt.free(Bool.cmp(bb, cb))
        case EQ{}:
          Eq.bit.absurd(&2,
            {tri(LT{}, Bool.cmp(bb, cb), Bool.cmp(ab, cb)) == True{} : Bool},
            ok)
        case GT{}:
          Eq.bit.absurd(&2,
            {tri(LT{}, Bool.cmp(bb, cb), GT{}) == True{} : Bool}, ok)
    case EQ{} LT{}:
      match z:
        case LT{}:
          tri.free.lt(Bool.cmp(ab, bb))
        case EQ{}:
          Eq.bit.absurd(&2,
            {tri(Bool.cmp(ab, bb), LT{}, Bool.cmp(ab, cb)) == True{} : Bool},
            ok)
        case GT{}:
          Eq.bit.absurd(&2,
            {tri(Bool.cmp(ab, bb), LT{}, GT{}) == True{} : Bool}, ok)
    case EQ{} EQ{}:
      match z:
        case LT{}:
          Eq.bit.absurd(&2,
            {tri(Bool.cmp(ab, bb), Bool.cmp(bb, cb), LT{}) == True{} : Bool},
            ok)
        case EQ{}:
          bool.tri(ab, bb, cb)
        case GT{}:
          Eq.bit.absurd(&2,
            {tri(Bool.cmp(ab, bb), Bool.cmp(bb, cb), GT{}) == True{} : Bool},
            ok)
    case LT{} GT{}:
      {==}
    case EQ{} GT{}:
      tri.mid.gt(Bool.cmp(ab, bb), Word.cmp.fin(ab, cb, z))
    case GT{} _:
      {==}

# LAW: three words compare consistently
law word.tri:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  {tri(Word.cmp(n, a, b), Word.cmp(n, b, c), Word.cmp(n, a, c)) == True{}
    : Bool}

def word.tri(n, a, b, c):
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          fin.tri(ab, bb, cb, Word.cmp(p, at, bt), Word.cmp(p, bt, ct),
            Word.cmp(p, at, ct), word.tri(p, at, bt, ct))

# the comparison of two chars, without the pair Base hands back with it
def chr.cmp(a: Char, b: Char) -> Cmp:
  match a b:
    case Chr{+x} Chr{+y}:
      U32.cmp(x, y)

# a lexicographic step: the first comparison unless it ties
def cmp.lex(c: Cmp, r: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      r
    case GT{}:
      GT{}

# LAW: comparing two numbers the other way round flips the answer
law u32.flip:
  for +x: U32
  for +y: U32
  {U32.cmp(y, x) == cmp.flip(U32.cmp(x, y)) : Cmp}

def u32.flip(x, y):
  match x y:
    case U32{+wx} U32{+wy}:
      word.flip(32n, wx, wy)

# LAW: three numbers compare consistently
law u32.tri:
  for +x: U32
  for +y: U32
  for +z: U32
  {tri(U32.cmp(x, y), U32.cmp(y, z), U32.cmp(x, z)) == True{} : Bool}

def u32.tri(x, y, z):
  match x y z:
    case U32{+wx} U32{+wy} U32{+wz}:
      word.tri(32n, wx, wy, wz)

# LAW: comparing two chars the other way round flips the answer
law chr.flip:
  for +a: Char
  for +b: Char
  {chr.cmp(b, a) == cmp.flip(chr.cmp(a, b)) : Cmp}

def chr.flip(a, b):
  match a b:
    case Chr{+x} Chr{+y}:
      u32.flip(x, y)

# LAW: three chars compare consistently
law chr.tri:
  for +a: Char
  for +b: Char
  for +c: Char
  {tri(chr.cmp(a, b), chr.cmp(b, c), chr.cmp(a, c)) == True{} : Bool}

def chr.tri(a, b, c):
  match a b c:
    case Chr{+x} Chr{+y} Chr{+z}:
      u32.tri(x, y, z)

# LAW: Base's walk in order, started from a comparison that is not a tie,
# answers that comparison: it reads no more of either string
law order.stays:
  for a: String
  for b: String
  for u: Cmp
  for ne: {Cmp.is_eq(u) == False{} : Bool}
  {String.order.go(a, b, u) == u : Cmp}

# every shape of the two strings, each with a start other than EQ
def order.stays(a, b, u, ne):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{y}, t2}:
      match u:
        case LT{}:
          {==}
        case EQ{}:
          Eq.bit.absurd2(&2, {LT{} == EQ{} : Cmp}, ne)
        case GT{}:
          {==}
    case SCon{Chr{x}, t1} SNil{}:
      match u:
        case LT{}:
          {==}
        case EQ{}:
          Eq.bit.absurd2(&2, {GT{} == EQ{} : Cmp}, ne)
        case GT{}:
          {==}
    case SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      match u:
        case LT{}:
          {==}
        case EQ{}:
          Eq.bit.absurd2(&2, {String.order.go(t1, t2, U32.cmp(x, y)) == EQ{} : Cmp}, ne)
        case GT{}:
          {==}

# LAW: one step of a string comparison, with the char comparison it turns on
# given as a parameter, since a match may not scrutinise a computed value.
# Base walks both strings once, carrying the comparison so far.
law order.cons.arm:
  for t1: String
  for t2: String
  for u: Cmp
  {String.order.go(t1, t2, u) == cmp.lex(u, String.order(t1, t2)) : Cmp}

def order.cons.arm(t1, t2, u):
  match u:
    case LT{}:
      order.stays(t1, t2, LT{}, {==})
    case EQ{}:
      {==}
    case GT{}:
      order.stays(t1, t2, GT{}, {==})

# LAW: two strings are compared by their first chars, and by the rest of them
# only when those tie
law order.cons:
  for +h1: Char
  for t1: String
  for +h2: Char
  for t2: String
  {String.order(SCon{h1, t1}, SCon{h2, t2})
    == cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)) : Cmp}

def order.cons(h1, t1, h2, t2):
  match h1 h2:
    case Chr{+x1} Chr{+x2}:
      order.cons.arm(t1, t2, U32.cmp(x1, x2))

# LAW: a lexicographic step taken the other way round flips the answer
law lex.flip:
  for u: Cmp
  for r: Cmp
  {cmp.lex(cmp.flip(u), cmp.flip(r)) == cmp.flip(cmp.lex(u, r)) : Cmp}

def lex.flip(u, _r):
  match u:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# LAW: three lexicographic steps stay consistent when their parts do
law lex.tri:
  for u: Cmp
  for v: Cmp
  for w: Cmp
  for r1: Cmp
  for r2: Cmp
  for r3: Cmp
  for tu: {tri(u, v, w) == True{} : Bool}
  for tr: {tri(r1, r2, r3) == True{} : Bool}
  {tri(cmp.lex(u, r1), cmp.lex(v, r2), cmp.lex(w, r3)) == True{} : Bool}

def lex.tri(u, v, w, r1, r2, r3, tu, tr):
  match u v:
    case LT{} LT{}:
      match w:
        case LT{}:
          {==}
        case EQ{}:
          Eq.bit.absurd(&2, {Cmp.is_lt(r3) == True{} : Bool}, tu)
        case GT{}:
          tu
    case LT{} EQ{}:
      match w:
        case LT{}:
          tri.lt.free(r2)
        case EQ{}:
          Eq.bit.absurd(&2, {tri(LT{}, r2, r3) == True{} : Bool}, tu)
        case GT{}:
          Eq.bit.absurd(&2, {tri(LT{}, r2, GT{}) == True{} : Bool}, tu)
    case EQ{} LT{}:
      match w:
        case LT{}:
          tri.free.lt(r1)
        case EQ{}:
          Eq.bit.absurd(&2, {tri(r1, LT{}, r3) == True{} : Bool}, tu)
        case GT{}:
          Eq.bit.absurd(&2, {tri(r1, LT{}, GT{}) == True{} : Bool}, tu)
    case EQ{} EQ{}:
      match w:
        case LT{}:
          Eq.bit.absurd(&2, {tri(r1, r2, LT{}) == True{} : Bool}, tu)
        case EQ{}:
          tr
        case GT{}:
          Eq.bit.absurd(&2, {tri(r1, r2, GT{}) == True{} : Bool}, tu)
    case LT{} GT{}:
      {==}
    case EQ{} GT{}:
      tri.mid.gt(r1, cmp.lex(w, r3))
    case GT{} _:
      {==}

# LAW: comparing two strings the other way round flips the answer
law str.flip:
  for +a: String
  for +b: String
  {String.order(b, a) == cmp.flip(String.order(a, b)) : Cmp}

def str.flip(a, b):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{Chr{x2}, t2}:
      {==}
    case SCon{Chr{x1}, t1} SNil{}:
      {==}
    case SCon{+h1, +t1} SCon{+h2, +t2}:
      Equal.trans(Cmp,
        String.order(SCon{h2, t2}, SCon{h1, t1}),
        cmp.lex(chr.cmp(h2, h1), String.order(t2, t1)),
        cmp.flip(String.order(SCon{h1, t1}, SCon{h2, t2})),
        order.cons(h2, t2, h1, t1),
        Equal.trans(Cmp,
          cmp.lex(chr.cmp(h2, h1), String.order(t2, t1)),
          cmp.lex(cmp.flip(chr.cmp(h1, h2)), cmp.flip(String.order(t1, t2))),
          cmp.flip(String.order(SCon{h1, t1}, SCon{h2, t2})),
          Equal.trans(Cmp,
            cmp.lex(chr.cmp(h2, h1), String.order(t2, t1)),
            cmp.lex(cmp.flip(chr.cmp(h1, h2)), String.order(t2, t1)),
            cmp.lex(cmp.flip(chr.cmp(h1, h2)), cmp.flip(String.order(t1, t2))),
            Equal.cong(Cmp, Cmp, u => cmp.lex(u, String.order(t2, t1)),
              chr.cmp(h2, h1), cmp.flip(chr.cmp(h1, h2)), chr.flip(h1, h2)),
            Equal.cong(Cmp, Cmp,
              r => cmp.lex(cmp.flip(chr.cmp(h1, h2)), r),
              String.order(t2, t1), cmp.flip(String.order(t1, t2)),
              str.flip(t1, t2))),
          Equal.trans(Cmp,
            cmp.lex(cmp.flip(chr.cmp(h1, h2)), cmp.flip(String.order(t1, t2))),
            cmp.flip(cmp.lex(chr.cmp(h1, h2), String.order(t1, t2))),
            cmp.flip(String.order(SCon{h1, t1}, SCon{h2, t2})),
            lex.flip(chr.cmp(h1, h2), String.order(t1, t2)),
            Equal.cong(Cmp, Cmp, w => cmp.flip(w),
              cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
              String.order(SCon{h1, t1}, SCon{h2, t2}),
              Equal.sym(Cmp, String.order(SCon{h1, t1}, SCon{h2, t2}),
                cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
                order.cons(h1, t1, h2, t2))))))

# LAW: three strings that all have a first char compare by those chars, and by
# their tails where the chars tie, so consistency at both levels is
# consistency of the whole
law str.tri.go:
  for +h1: Char
  for +t1: String
  for +h2: Char
  for +t2: String
  for +h3: Char
  for +t3: String
  for ih: {tri(String.order(t1, t2), String.order(t2, t3),
    String.order(t1, t3)) == True{} : Bool}
  {tri(String.order(SCon{h1, t1}, SCon{h2, t2}),
    String.order(SCon{h2, t2}, SCon{h3, t3}),
    String.order(SCon{h1, t1}, SCon{h3, t3})) == True{} : Bool}

def str.tri.go(h1, t1, h2, t2, h3, t3, ih):
  Equal.trans(Bool,
    tri(String.order(SCon{h1, t1}, SCon{h2, t2}),
      String.order(SCon{h2, t2}, SCon{h3, t3}),
      String.order(SCon{h1, t1}, SCon{h3, t3})),
    tri(cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
      cmp.lex(chr.cmp(h2, h3), String.order(t2, t3)),
      cmp.lex(chr.cmp(h1, h3), String.order(t1, t3))),
    True{},
    Equal.trans(Bool,
      tri(String.order(SCon{h1, t1}, SCon{h2, t2}),
        String.order(SCon{h2, t2}, SCon{h3, t3}),
        String.order(SCon{h1, t1}, SCon{h3, t3})),
      tri(cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
        String.order(SCon{h2, t2}, SCon{h3, t3}),
        String.order(SCon{h1, t1}, SCon{h3, t3})),
      tri(cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
        cmp.lex(chr.cmp(h2, h3), String.order(t2, t3)),
        cmp.lex(chr.cmp(h1, h3), String.order(t1, t3))),
      Equal.cong(Cmp, Bool,
        u => tri(u, String.order(SCon{h2, t2}, SCon{h3, t3}),
          String.order(SCon{h1, t1}, SCon{h3, t3})),
        String.order(SCon{h1, t1}, SCon{h2, t2}),
        cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
        order.cons(h1, t1, h2, t2)),
      Equal.trans(Bool,
        tri(cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
          String.order(SCon{h2, t2}, SCon{h3, t3}),
          String.order(SCon{h1, t1}, SCon{h3, t3})),
        tri(cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
          cmp.lex(chr.cmp(h2, h3), String.order(t2, t3)),
          String.order(SCon{h1, t1}, SCon{h3, t3})),
        tri(cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
          cmp.lex(chr.cmp(h2, h3), String.order(t2, t3)),
          cmp.lex(chr.cmp(h1, h3), String.order(t1, t3))),
        Equal.cong(Cmp, Bool,
          v => tri(cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)), v,
            String.order(SCon{h1, t1}, SCon{h3, t3})),
          String.order(SCon{h2, t2}, SCon{h3, t3}),
          cmp.lex(chr.cmp(h2, h3), String.order(t2, t3)),
          order.cons(h2, t2, h3, t3)),
        Equal.cong(Cmp, Bool,
          w => tri(cmp.lex(chr.cmp(h1, h2), String.order(t1, t2)),
            cmp.lex(chr.cmp(h2, h3), String.order(t2, t3)), w),
          String.order(SCon{h1, t1}, SCon{h3, t3}),
          cmp.lex(chr.cmp(h1, h3), String.order(t1, t3)),
          order.cons(h1, t1, h3, t3)))),
    lex.tri(chr.cmp(h1, h2), chr.cmp(h2, h3), chr.cmp(h1, h3),
      String.order(t1, t2), String.order(t2, t3), String.order(t1, t3),
      chr.tri(h1, h2, h3), ih))

# LAW: three strings compare consistently: the comparison is a total order,
# so what two of the three answers leave room for is what the third answers
law str.tri:
  for +a: String
  for +b: String
  for +c: String
  {tri(String.order(a, b), String.order(b, c), String.order(a, c)) == True{}
    : Bool}

def str.tri(a, b, c):
  match a b c:
    case SNil{} SNil{} SNil{}:
      {==}
    case SNil{} SNil{} SCon{Chr{x3}, t3}:
      {==}
    case SNil{} SCon{Chr{x2}, t2} SNil{}:
      {==}
    case SNil{} SCon{Chr{x2}, t2} SCon{Chr{x3}, t3}:
      tri.lt.free(String.order(SCon{Chr{x2}, t2}, SCon{Chr{x3}, t3}))
    case SCon{Chr{x1}, t1} SNil{} SNil{}:
      {==}
    case SCon{Chr{x1}, t1} SNil{} SCon{Chr{x3}, t3}:
      {==}
    case SCon{Chr{x1}, t1} SCon{Chr{x2}, t2} SNil{}:
      tri.mid.gt(String.order(SCon{Chr{x1}, t1}, SCon{Chr{x2}, t2}), GT{})
    case SCon{+h1, +t1} SCon{+h2, +t2} SCon{+h3, +t3}:
      str.tri.go(h1, t1, h2, t2, h3, t3, str.tri(t1, t2, t3))

# The path algebra begins here. Most of these laws are a hypothesis rewritten
# into a `Bool.pick` cascade, which is why every hypothesis in the law files is
# written constant first: `%e` rewrites the right of an equation back into the
# left, so an equation read the other way round does not reach the goal. The
# rest is induction, on a string for the split and on a list for the walk.

# The three tests `comp_of` makes, refused one after another: an empty
# component, then `.`, then `..`. What is left is the arm that keeps the text.
def L2.comp_name(c, e0, e1, e2):
  %e0 : {Bool.pick(Path.Comp, Bool.or(_, String.eq(c, ".")), Path.CSkip{},
    Bool.pick(Path.Comp, String.eq(c, ".."), Path.CUp{}, Path.CName{c}))
    == Path.CName{c} : Path.Comp}
  %e1 : {Bool.pick(Path.Comp, Bool.or(False{}, _), Path.CSkip{},
    Bool.pick(Path.Comp, String.eq(c, ".."), Path.CUp{}, Path.CName{c}))
    == Path.CName{c} : Path.Comp}
  %e2 : {Bool.pick(Path.Comp, Bool.or(False{}, False{}), Path.CSkip{},
    Bool.pick(Path.Comp, _, Path.CUp{}, Path.CName{c}))
    == Path.CName{c} : Path.Comp}
  {==}

# LAW: one component against the root flag. None of the three arms touches
# it: a skip keeps the walk as it was, a climb rewrites only what was kept,
# and a name is pushed onto what was kept.
law walk_keeps_root.step:
  for w: Path.Walk
  for c: Path.Comp
  {L7.walk.abs(Path.norm.go(w, c)) == L7.walk.abs(w) : Bool}

def walk_keeps_root.step(w, c):
  match w:
    case Path.Walk{abs, out}:
      match c:
        case Path.CSkip{}:
          {==}
        case Path.CUp{}:
          {==}
        case Path.CName{s}:
          {==}

# By induction on the components, with the step above carrying each one.
def L7.walk_keeps_root(cs, w):
  match cs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(Bool,
        L7.walk.abs(Path.norm.walk(t, Path.norm.go(w, Path.comp_of(h)))),
        L7.walk.abs(Path.norm.go(w, Path.comp_of(h))),
        L7.walk.abs(w),
        L7.walk_keeps_root(t, Path.norm.go(w, Path.comp_of(h))),
        walk_keeps_root.step(w, Path.comp_of(h)))

# LAW: a normalisation that ends at the root writes the root back. The
# components it kept are never read: whatever they are, the text opens with a
# separator.
law fin_abs:
  for w: Path.Walk
  for e: {L7.walk.abs(w) == True{} : Bool}
  {String.starts_with(Path.norm.fin(w), "/") == True{} : Bool}

def fin_abs(w, e):
  match w:
    case Path.Walk{abs, out}:
      match abs:
        case True{}:
          Eq.starts_nil(String.join(List.reverse(&2, String, out), "/"))
        case False{}:
          Eq.bit.absurd(&2,
            {String.starts_with(Path.norm.fin(Path.Walk{False{}, out}), "/")
              == True{} : Bool}, e)

# The root flag a normalisation starts with is the answer to the very test the
# law assumes, so the hypothesis rewrites it to True and the walk carries it
# to the end.
def L3.norm_absolute(p, e):
  %e : {String.starts_with(Path.norm.fin(Path.norm.walk(String.split(p, '/'),
    Path.Walk{_, []})), "/") == True{} : Bool}
  fin_abs(Path.norm.walk(String.split(p, '/'), Path.Walk{True{}, []}),
    L7.walk_keeps_root(String.split(p, '/'), Path.Walk{True{}, []}))

# LAW: a dependency appended to a list the drop already cleaned is dropped
# again by the same name
law without_append:
  for xs: List<&2, M.Dep>
  for +d: M.Dep
  {Rend.without(List.append(&2, M.Dep, xs, [d]), M.dep.name(d))
    == Rend.without(xs, M.dep.name(d)) : List<&2, M.Dep>}

def without_append(xs, d):
  match xs:
    case []:
      Equal.cong(Bool, List<&2, M.Dep>,
        b => Rend.without.put(b, d, []), String.eq(M.dep.name(d), M.dep.name(d)),
        True{}, Eq.string_eq_self(M.dep.name(d)))
    case +h <> t:
      Equal.cong(List<&2, M.Dep>, List<&2, M.Dep>,
        y => Rend.without.put(String.eq(M.dep.name(h), M.dep.name(d)), h, y),
        Rend.without(List.append(&2, M.Dep, t, [d]), M.dep.name(d)),
        Rend.without(t, M.dep.name(d)),
        without_append(t, d))

def L1.add_idem(m, d):
  match m:
    case M.Manifest{+n, +e, +b, +hb, +hbpa, +hbpv, +ds, +ts}:
      Equal.cong(List<&2, M.Dep>, M.Manifest,
        y => M.Manifest{n, e, b, hb, hbpa, hbpv, List.append(&2, M.Dep, y, [d]), ts},
        Rend.without(List.append(&2, M.Dep, Rend.without(ds, M.dep.name(d)), [d]),
          M.dep.name(d)),
        Rend.without(ds, M.dep.name(d)),
        Equal.trans(List<&2, M.Dep>,
          Rend.without(List.append(&2, M.Dep, Rend.without(ds, M.dep.name(d)), [d]),
            M.dep.name(d)),
          Rend.without(Rend.without(ds, M.dep.name(d)), M.dep.name(d)),
          Rend.without(ds, M.dep.name(d)),
          without_append(Rend.without(ds, M.dep.name(d)), d),
          L9.without_idem(ds, M.dep.name(d))))

# Idempotence. `I.lines` run again on the lines it made gives them back. Its
# output has no `.ez/` line, holds the three rules when it holds a hash, and
# holds the vendored hashes' lines as one block; so the second run keeps every
# line it is given and puts that same block where the first run did.

# whether a kind of line is one the walk keeps as it is. Law vocabulary: ez
# never calls it.
def keeps(k: I.Rule) -> Bool:
  match k:
    case I.Other{}:
      True{}
    case I.Dir{}:
      False{}
    case I.Star{}:
      True{}
    case I.Lib{}:
      True{}
    case I.Pkgs{}:
      True{}
    case I.Allow{_h}:
      False{}

# ---------------------------------------------------------------------------
# the hub packages the package imports: the upload is reached only past a
# World in which every one of them is on the hub

# LAW: the questions about the hub are none of them the upload
law asks_quiet:
  for +hub: String
  for ps: List<&2, PP.Probe>
  {PP.any.upload(PP.probe.asks(hub, ps)) == False{} : Bool}

def asks_quiet(hub, ps):
  match ps:
    case []:
      {==}
    case _h <> t:
      asks_quiet(hub, t)

# LAW: the hub stage gets as far as the upload only when every hub import is
# on the hub. Still asking is asking the hub, not bend, and off the hub stops.
law on_hub:
  for h: PP.Hubbed
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.hub(h, w)) == True{} : Bool}
  {PP.on.hub.v(h) == True{} : Bool}

def on_hub(h, w, s):
  match h:
    case PP.OnHub{}:
      {==}
    case PP.HubWait{open}:
      Eq.bit.absurd(&2, {PP.on.hub.v(PP.HubWait{open}) == True{} : Bool},
        Equal.trans(Bool, False{}, PP.any.upload(PP.probe.asks(PP.hub(w), open)), True{},
          Equal.sym(Bool, PP.any.upload(PP.probe.asks(PP.hub(w), open)), False{},
            asks_quiet(PP.hub(w), open)),
          s))
    case PP.OffHub{why}:
      Eq.bit.absurd(&2, {PP.on.hub.v(PP.OffHub{why}) == True{} : Bool}, s)

law hub_lock.got:
  for got: PW.Heard
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.lock(True{}, got, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_lock.got(got, w, s):
  match got:
    case PW.Open{}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case PW.Heard{_a}:
      on_hub(PP.hubbed(w), w, s)

law hub_lock:
  for need: Bool
  for got: PW.Heard
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.lock(need, got, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_lock(need, got, w, s):
  match need:
    case False{}:
      on_hub(PP.hubbed(w), w, s)
    case True{}:
      hub_lock.got(got, w, s)

law hub_kept:
  for k: PP.Kept
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.kept(k, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_kept(k, w, s):
  match k:
    case PP.Kept{}:
      hub_lock(PP.any(PP.nvs(w)), PW.heard(w, PW.Lock{}), w, s)
    case PP.Stray{_path}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case PP.KeptWait{}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case PP.KeptNo{_why}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)

law hub_walk:
  for k: K.Walked
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.walk(k, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_walk(k, w, s):
  match k:
    case K.Walked{_h, _root, _fs, _sums}:
      hub_kept(PP.stray(w), w, s)
    case K.Asks{_at}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case K.Refused{_why}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)

law hub_clean:
  for b: Bool
  for +text: String
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.clean(b, text, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_clean(b, _text, w, s):
  match b:
    case True{}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case False{}:
      hub_walk(PP.walked(w), w, s)

law hub_status:
  for st: PP.Status
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.status(st, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_status(st, w, s):
  match st:
    case PP.Said{+text}:
      hub_clean(PP.dirty(text), text, w, s)
    case PP.StatusWait{}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)
    case PP.StatusNo{_why}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)

law hub_led:
  for l: PP.Led
  for +w: PW.World
  for s: {PP.sends.v(PP.decide.led(l, w)) == True{} : Bool}
  {PP.on.hub(w) == True{} : Bool}

def hub_led(l, w, s):
  match l:
    case PP.Led{_e, _nv}:
      hub_status(PP.status(w), w, s)
    case PP.LedNo{_why}:
      Eq.bit.absurd(&2, {PP.on.hub(w) == True{} : Bool}, s)

def L4.pub_sends_only_on_hub(w, s):
  hub_led(PP.led(w), w, s)

# LAW: a bit that is True only when every hub import is on the hub is False
# when one is not
law off_flip:
  for b: Bool
  for +w: PW.World
  for f: {b == True{} : Bool} -> {PP.on.hub(w) == True{} : Bool}
  for e: {PP.on.hub(w) == False{} : Bool}
  {b == False{} : Bool}

def off_flip(b, w, f, e):
  match b:
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool},
        Equal.trans(Bool, False{}, PP.on.hub(w), True{},
          Equal.sym(Bool, PP.on.hub(w), False{}, e), f({==})))
    case False{}:
      {==}

def L4.pub_offhub_sends_nothing(w, why, e):
  off_flip(PP.sends(w), w, x => L4.pub_sends_only_on_hub(w, x),
    Equal.cong(PP.Hubbed, Bool, x => PP.on.hub.v(x), PP.hubbed(w), PP.OffHub{why}, e))

# The walk's sources, one step at a time. Each lemma is one def of the step,
# with the value it branches on given as a parameter.

# LAW: a package resolved by its verdict carries the ledger's source
law verdict_pins:
  for +ns: List<&2, L.Name>
  for v: W.Verdict
  for +orgs: List<&2, L.Origin>
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {D1.pinned.all(orgs, packs) == packs : List<&2, L.Pack>}
  {D1.pinned.all(orgs, P.walk.packs(P.step.verdict(v, ns, L.origin(orgs, hash),
    hash, rest, packs, asks, bad)))
    == P.walk.packs(P.step.verdict(v, ns, L.origin(orgs, hash), hash, rest, packs,
      asks, bad)) : List<&2, L.Pack>}

def verdict_pins(_ns, v, orgs, hash, _rest, packs, _asks, _bad, e):
  match v:
    case W.No{_why}:
      e
    case W.Ok{fs, _ss}:
      Equal.cong(List<&2, L.Pack>, List<&2, L.Pack>,
        ps => L.Pack{hash, L.origin(orgs, hash), fs} <> ps,
        D1.pinned.all(orgs, packs), packs, e)
    case W.Named{_names}:
      e

# LAW: and one looked up, whether it was answered or not
law look_pins:
  for +ns: List<&2, L.Name>
  for found: P.Look
  for +orgs: List<&2, L.Origin>
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {D1.pinned.all(orgs, packs) == packs : List<&2, L.Pack>}
  {D1.pinned.all(orgs, P.walk.packs(P.step.look(found, ns, L.origin(orgs, hash),
    hash, rest, packs, asks, bad)))
    == P.walk.packs(P.step.look(found, ns, L.origin(orgs, hash), hash, rest, packs,
      asks, bad)) : List<&2, L.Pack>}

def look_pins(ns, found, orgs, hash, rest, packs, asks, bad, e):
  match found:
    case P.Absent{}:
      e
    case P.Found{v}:
      verdict_pins(ns, v, orgs, hash, rest, packs, asks, bad, e)

# LAW: and one passed over, or picked
law pick_pins:
  for +ns: List<&2, L.Name>
  for seen: Bool
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for +hash: String
  for rest: List<&2, String>
  for +packs: List<&2, L.Pack>
  for asks: List<&2, String>
  for bad: String
  for e: {D1.pinned.all(orgs, packs) == packs : List<&2, L.Pack>}
  {D1.pinned.all(orgs, P.walk.packs(P.step.pick(seen, orgs, ns, js, hash, rest,
    packs, asks, bad)))
    == P.walk.packs(P.step.pick(seen, orgs, ns, js, hash, rest, packs, asks, bad))
    : List<&2, L.Pack>}

def pick_pins(ns, seen, orgs, js, hash, rest, packs, asks, bad, e):
  match seen:
    case True{}:
      e
    case False{}:
      look_pins(ns, P.look(js, hash), orgs, hash, rest, packs, asks, bad, e)

# LAW: and one step of the walk, whatever the queue held
law pop_pins:
  for +ns: List<&2, L.Name>
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for queue: List<&2, String>
  for +packs: List<&2, L.Pack>
  for +asks: List<&2, String>
  for bad: String
  for e: {D1.pinned.all(orgs, packs) == packs : List<&2, L.Pack>}
  {D1.pinned.all(orgs, P.walk.packs(P.step.pop(orgs, ns, js, queue, packs, asks,
    bad)))
    == P.walk.packs(P.step.pop(orgs, ns, js, queue, packs, asks, bad))
    : List<&2, L.Pack>}

def pop_pins(ns, orgs, js, queue, packs, asks, bad, e):
  match queue:
    case []:
      e
    case +h <> t:
      pick_pins(ns, Bool.or(L.has(packs, h), L.seen.holds(asks, h)), orgs, js, h, t,
        packs, asks, bad, e)

# LAW: one step keeps every resolved package on the ledger's source
law step_pins:
  for +ns: List<&2, L.Name>
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for wk: P.Walk
  for e: {D1.pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  {D1.pinned.all(orgs, P.walk.packs(P.walk.step(orgs, ns, js, wk)))
    == P.walk.packs(P.walk.step(orgs, ns, js, wk)) : List<&2, L.Pack>}

def step_pins(ns, orgs, js, wk, e):
  match wk:
    case P.Walk{queue, packs, asks, bad}:
      pop_pins(ns, orgs, js, queue, packs, asks, bad, e)

# LAW: a walk that ran out of fuel keeps the packages it had
law out_pins:
  for done: Bool
  for +orgs: List<&2, L.Origin>
  for wk: P.Walk
  for e: {D1.pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  {D1.pinned.all(orgs, P.walk.packs(P.walk.out(done, wk)))
    == P.walk.packs(P.walk.out(done, wk)) : List<&2, L.Pack>}

def out_pins(done, _orgs, wk, e):
  match done:
    case True{}:
      e
    case False{}:
      match wk:
        case P.Walk{_queue, _packs, _asks, _bad}:
          e

# LAW: a walk that is done is what it was, and one that is not goes on
law more_pins:
  for +ns: List<&2, L.Name>
  for done: Bool
  for +orgs: List<&2, L.Origin>
  for +js: List<&2, W.Judged>
  for f: Nat
  for +wk: P.Walk
  for e: {D1.pinned.all(orgs, P.walk.packs(wk)) == P.walk.packs(wk)
    : List<&2, L.Pack>}
  for ih: {D1.pinned.all(orgs, P.walk.packs(P.walk(f, orgs, ns, js,
    P.walk.step(orgs, ns, js, wk))))
    == P.walk.packs(P.walk(f, orgs, ns, js, P.walk.step(orgs, ns, js, wk)))
    : List<&2, L.Pack>}
  {D1.pinned.all(orgs, P.walk.packs(P.walk.more(done, wk,
    now => P.walk(f, orgs, ns, js, P.walk.step(orgs, ns, js, now)))))
    == P.walk.packs(P.walk.more(done, wk,
      now => P.walk(f, orgs, ns, js, P.walk.step(orgs, ns, js, now)))) : List<&2, L.Pack>}

def more_pins(_ns, done, _orgs, _js, _f, _wk, e, ih):
  match done:
    case True{}:
      e
    case False{}:
      ih

def L8.walk_pins_ledger_sources(fuel, orgs, ns, js, wk, e):
  match fuel:
    case 0n:
      out_pins(P.walk.done(wk), orgs, wk, e)
    case 1n+f:
      more_pins(ns, P.walk.done(wk), orgs, js, f, wk, e,
        L8.walk_pins_ledger_sources(f, orgs, ns, js, P.walk.step(orgs, ns, js, wk),
          step_pins(ns, orgs, js, wk, e)))

# LAW: the head of a scan that answered False
law any_head:
  for c: Bool
  for r: Unit -> Bool
  for e: {L.any.step(c, r) == False{} : Bool}
  {c == False{} : Bool}

def any_head(c, _r, e):
  match c:
    case False{}:
      {==}
    case True{}:
      e

# LAW: and the rest of it
law any_rest:
  for c: Bool
  for r: Unit -> Bool
  for e: {L.any.step(c, r) == False{} : Bool}
  {r(Unit{}) == False{} : Bool}

def any_rest(c, r, e):
  match c:
    case False{}:
      e
    case True{}:
      Eq.bit.absurd2(&2, {r(Unit{}) == False{} : Bool}, e)

# LAW: an `and` of two halves that answered True
law and_true:
  for u: Bool
  for v: Bool
  for eu: {u == True{} : Bool}
  for ev: {v == True{} : Bool}
  {Bool.and(u, v) == True{} : Bool}

def and_true(u, _v, eu, ev):
  match u:
    case True{}:
      ev
    case False{}:
      eu

# laws/UpgradeOnlyNamedPackage.bend, the tools, in the shape of the
# dependencies above: one tool's pin keeps its name, and one of another name
# is not chosen, so it is left.

# the name a tool's pin leaves in the ledger, or `x` when it leaves none
def pinned.name(p: Up.Pinned, x: String) -> String:
  match p:
    case Up.Pinned{t, _moved, _says}:
      M.tool.name(t)
    case Up.PinWait{_asks}:
      x
    case Up.PinHalt{_why}:
      x

# LAW: a pin with a commit written in keeps its name
law set_name:
  for tool: M.Cli
  for rev: String
  for tag: String
  for nar: String
  {M.tool.name(Up.set(tool, rev, tag, nar)) == M.tool.name(tool) : String}

def set_name(tool, _rev, _tag, _nar):
  match tool:
    case M.Cli{n, e, b, s}:
      match s:
        case M.Hub{hv}:
          {==}
        case M.Git{url, r, old, root, nr, vend}:
          {==}
        case M.Member{mp, mn}:
          {==}

law tpin_name:
  for short: Bool
  for +tool: M.Cli
  for +rev: String
  for +tag: String
  for +nar: String
  for says: List<&2, String>
  {pinned.name(Up.tool.pin(short, tool, rev, tag, nar, says), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tpin_name(short, tool, rev, tag, nar, _says):
  match short:
    case True{}:
      {==}
    case False{}:
      set_name(tool, rev, tag, nar)

law weighed_name:
  for wd: Up.Wd
  for +tool: M.Cli
  for +rev: String
  for +tag: String
  for says: List<&2, String>
  {pinned.name(Up.tool.weighed(wd, tool, rev, tag, says), M.tool.name(tool))
    == M.tool.name(tool) : String}

def weighed_name(wd, tool, rev, tag, says):
  match wd:
    case Up.Wd{+nar}:
      tpin_name(Bool.or(String.is_empty(rev), String.is_empty(nar)), tool, rev, tag, nar, says)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law resolved_name:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +ref: String
  {pinned.name(Up.tool.resolved(tip, rs, tool, ref), M.tool.name(tool)) == M.tool.name(tool) : String}

def resolved_name(tip, rs, tool, ref):
  match tip:
    case Up.At{+rev, _tag, _branch}:
      weighed_name(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, ref, [])
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law named_name:
  for named: Up.Named
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +url: String
  {pinned.name(Up.tool.named(named, rs, tool, url), M.tool.name(tool)) == M.tool.name(tool) : String}

def named_name(named, rs, tool, url):
  match named:
    case Up.Named{+ref}:
      resolved_name(Up.follow(rs, url, ref), rs, tool, ref)
    case Up.NamedWait{_ask}:
      {==}
    case Up.NamedNo{_why}:
      {==}

law tverdict_name:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +branch: String
  {pinned.name(Up.tool.verdict(verdict, rs, tool, tip, branch), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tverdict_name(verdict, rs, tool, _tip, branch):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, _tag}:
      weighed_name(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, "",
        [Up.say.move(M.tool.name(tool), M.source.rev(M.tool.source(tool)), rev, branch)])

law tkept_nar_name:
  for fill: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  for +nar: String
  {pinned.name(Up.tool.kept.nar(fill, rs, tool, tip, tag, nar), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tkept_nar_name(fill, rs, tool, tip, tag, nar):
  match fill:
    case True{}:
      tpin_name(Bool.or(String.is_empty(tip), String.is_empty(nar)), tool, tip, "", nar, [])
    case False{}:
      tverdict_name(U.judge(True{}, True{}, String.eq(M.source.nar(M.tool.source(tool)), nar), tip, tag),
        rs, tool, tip, "")

law tkept_name:
  for wd: Up.Wd
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  {pinned.name(Up.tool.kept(wd, rs, tool, tip, tag), M.tool.name(tool)) == M.tool.name(tool) : String}

def tkept_name(wd, rs, tool, tip, tag):
  match wd:
    case Up.Wd{+nar}:
      tkept_nar_name(String.is_empty(M.source.nar(M.tool.source(tool))), rs, tool, tip, tag, nar)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law tonward_name:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  for +branch: String
  {pinned.name(Up.tool.onward(asc, rs, tool, tip, tag, branch), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tonward_name(asc, rs, tool, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      tverdict_name(U.judge(False{}, yes, False{}, tip, tag), rs, tool, tip, branch)
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law tsame_name:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  for +branch: String
  {pinned.name(Up.tool.same(same, rs, tool, tip, tag, branch), M.tool.name(tool))
    == M.tool.name(tool) : String}

def tsame_name(same, rs, tool, tip, tag, branch):
  match same:
    case True{}:
      tkept_name(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool))}), rs, tool, tip, tag)
    case False{}:
      tonward_name(Up.onward(rs, Up.Above{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool)), tip}), rs, tool, tip, tag, branch)

law ttip_name:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pinned.name(Up.tool.tip(tip, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def ttip_name(tip, rs, tool):
  match tip:
    case Up.At{+rev, tag, branch}:
      tsame_name(String.eq(M.source.rev(M.tool.source(tool)), rev), rs, tool, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law taim_name:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pinned.name(Up.tool.aim(aim, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def taim_name(aim, rs, tool):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      ttip_name(Up.follow(rs, M.source.url(M.tool.source(tool)), ref), rs, tool)
    case U.Forward{}:
      ttip_name(Up.forward(rs, M.source.url(M.tool.source(tool))), rs, tool)

law fill_name:
  for no_rev: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pinned.name(Up.tool.fill(no_rev, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def fill_name(no_rev, rs, tool):
  match no_rev:
    case True{}:
      named_name(Up.tool.ref(String.is_empty(M.source.tag(M.tool.source(tool))), rs,
        M.source.url(M.tool.source(tool)), M.source.tag(M.tool.source(tool))), rs, tool,
        M.source.url(M.tool.source(tool)))
    case False{}:
      taim_name(U.aim(True{}, M.tool.source(tool)), rs, tool)

law short_name:
  for short: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pinned.name(Up.tool.short(short, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def short_name(short, rs, tool):
  match short:
    case True{}:
      fill_name(String.is_empty(M.source.rev(M.tool.source(tool))), rs, tool)
    case False{}:
      taim_name(U.aim(True{}, M.tool.source(tool)), rs, tool)

law git_name:
  for git: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pinned.name(Up.tool.git(git, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def git_name(git, rs, tool):
  match git:
    case False{}:
      {==}
    case True{}:
      short_name(Bool.or(String.is_empty(M.source.rev(M.tool.source(tool))),
        String.is_empty(M.source.nar(M.tool.source(tool)))), rs, tool)

# LAW: whatever the upgrade makes of one tool, what it leaves in the ledger has
# the tool's name
law sel_name:
  for sel: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pinned.name(Up.tool.sel(sel, rs, tool), M.tool.name(tool)) == M.tool.name(tool) : String}

def sel_name(sel, rs, tool):
  match sel:
    case False{}:
      {==}
    case True{}:
      git_name(M.source.is_git(M.tool.source(tool)), rs, tool)

# what every fate keeps: the name of the dependency it leaves, and at least
# one question when it waits
def mv.fine(fate: Up.Fate, +name: String) -> String & Bool:
  match fate:
    case Up.Became{d, _o, _n, _p, _m, _s, _t}:
      (M.dep.name(d), True{})
    case Up.Waits{asks}:
      (name, Bool.not(List.is_empty(&2, Up.Ask, asks)))
    case Up.Halts{_why}:
      (name, True{})

def mv.fst(p: String & Bool) -> String:
  (a, _b) = p
  a

def mv.snd(p: String & Bool) -> Bool:
  (_a, b) = p
  b

# LAW: an `or` whose right half answered True
law mv.or_r:
  for a: Bool
  for b: Bool
  for e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def mv.or_r(a, _b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

# LAW: an `or` whose left half answered True
law mv.or_l:
  for a: Bool
  for +b: Bool
  for e: {a == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def mv.or_l(a, b, e):
  Equal.cong(Bool, Bool, x => Bool.or(x, b), a, True{}, e)

# LAW: a refusal's reason is never empty
law mv.halt_ne:
  for why: String
  {String.is_empty(Up.halt.why(why)) == False{} : Bool}

def mv.halt_ne(why):
  match why:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

# LAW: and so it reads as a refusal
law mv.halt_not:
  for why: String
  {Bool.not(String.is_empty(Up.halt.why(why))) == True{} : Bool}

def mv.halt_not(why):
  match why:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

# Every fate keeps its dependency's name, and waits only with a question. The
# walk reads the name to find a dependency again, and a question to tell a
# walk that waits from one that is done.

# LAW: a pin moved, once the hub has had its word
law mv.fine_hub:
  for hb: Up.Hubbed
  for +hn: String
  for +hh: String
  for +he: String
  for src: M.Source
  for +hash: String
  for +r: String
  for +root2: String
  for +nar2: String
  for +man: String
  for srcs: List<&2, String>
  for +br: String
  {mv.fine(Up.dep.hub(hb, M.Dep{hn, hh, he, src}, hash, r, root2, nar2, man, srcs, br), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_hub(hb, _hn, _hh, _he, src, _hash, _r, _root2, _nar2, _man, _srcs, _br):
  match hb:
    case Up.Clear{}:
      match src:
        case M.Hub{hv}:
          {==}
        case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
          {==}
        case M.Member{mp, mn}:
          {==}
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

# LAW: a pin moved, once its checkout is in
law mv.fine_adv:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +r: String
  for +br: String
  {mv.fine(Up.dep.advance(co, rs, hub, M.Dep{hn, hh, he, src}, r, br), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_adv(co, rs, hub, hn, hh, he, src, r, br):
  match co:
    case Up.Co{nar2, root2, +man, srcs}:
      mv.fine_hub(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(man)}), hn, hh, he, src,
        Up.hash.of(man), r, root2, nar2, man, srcs, br)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: any verdict
law mv.fine_verdict:
  for v: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +br: String
  for +seen: String
  {mv.fine(Up.dep.verdict(v, rs, hub, M.Dep{hn, hh, he, src}, tip, br, seen), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_verdict(v, rs, hub, hn, hh, he, src, _tip, br, _seen):
  match v:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rv, _tg}:
      mv.fine_adv(Up.checkout(rs, Up.Tree{M.source.url(src), rv, he}), rs, hub, hn, hh, he, src,
        rv, br)

# LAW: the pin's own commit, once its checkout is in
law mv.fine_kept:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +tg: String
  {mv.fine(Up.dep.kept(co, rs, hub, M.Dep{hn, hh, he, src}, tip, tg), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_kept(co, rs, hub, hn, hh, he, src, tip, tg):
  match co:
    case Up.Co{nar2, root2, +man, _srcs}:
      mv.fine_verdict(U.judge(True{}, True{}, U.agree(hh, Up.hash.kept(hh, man), M.source.nar(src),
        nar2, M.source.root(src), root2), tip, tg), rs, hub, hn, hh, he, src, tip, "",
        Up.hash.kept(hh, man))
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: another commit, once ancestry is in
law mv.fine_onward:
  for a: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +tg: String
  for +br: String
  {mv.fine(Up.dep.onward(a, rs, hub, M.Dep{hn, hh, he, src}, tip, tg, br), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_onward(a, rs, hub, hn, hh, he, src, tip, tg, br):
  match a:
    case Up.Asc{yes}:
      mv.fine_verdict(U.judge(False{}, yes, False{}, tip, tg), rs, hub, hn, hh, he, src, tip, br, "")
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the tip against the pin
law mv.fine_same:
  for s: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  for +tip: String
  for +tg: String
  for +br: String
  {mv.fine(Up.dep.same(s, rs, hub, M.Dep{hn, hh, he, src}, tip, tg, br), hn)
    == (hn, True{}) : String & Bool}

def mv.fine_same(s, rs, hub, hn, hh, he, src, tip, tg, br):
  match s:
    case True{}:
      mv.fine_kept(Up.checkout(rs, Up.Tree{M.source.url(src), M.source.rev(src), he}), rs, hub,
        hn, hh, he, src, tip, tg)
    case False{}:
      mv.fine_onward(Up.onward(rs, Up.Above{M.source.url(src), M.source.rev(src), tip}), rs, hub,
        hn, hh, he, src, tip, tg, br)

# LAW: whatever tip the remote named
law mv.fine_tip:
  for t: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +src: M.Source
  {mv.fine(Up.dep.tip(t, rs, hub, M.Dep{hn, hh, he, src}), hn) == (hn, True{}) : String & Bool}

def mv.fine_tip(t, rs, hub, hn, hh, he, src):
  match t:
    case Up.At{+tip, +tg, +br}:
      mv.fine_same(String.eq(M.source.rev(src), tip), rs, hub, hn, hh, he, src, tip, tg, br)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: every dependency's fate, whatever it was asked
law mv.fine_one:
  for am: U.Aim
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +h: M.Dep
  {mv.fine(Up.dep.one(am, rs, only, hub, h), M.dep.name(h))
    == (M.dep.name(h), True{}) : String & Bool}

def mv.fine_one(am, rs, _only, hub, h):
  match am h:
    case U.Hold{} M.Dep{_hn, _hh, _he, _src}:
      {==}
    case U.Follow{+ref} M.Dep{+hn, +hh, +he, +src}:
      mv.fine_tip(Up.follow(rs, M.source.url(src), ref), rs, hub, hn, hh, he, src)
    case U.Forward{} M.Dep{+hn, +hh, +he, +src}:
      mv.fine_tip(Up.forward(rs, M.source.url(src)), rs, hub, hn, hh, he, src)

# LAW: a reason that is refused is not empty, so an upgrade that stops with
# it is not one whose stop is empty
law mv.halt_clash:
  for why: String
  for se: {String.is_empty(Up.halt.why(why)) == True{} : Bool}
  {False{} == True{} : Bool}

def mv.halt_clash(why, se):
  Equal.trans(Bool, False{}, String.is_empty(Up.halt.why(why)), True{},
    Equal.sym(Bool, String.is_empty(Up.halt.why(why)), False{}, mv.halt_ne(why)), se)

# ---------------------------------------------------------------------------
# laws/LockIdempotent.bend for `ez lock --upgrade`: run again on the World
# it leaves, against a remote that did not change, it moves nothing, writes
# the same lock, writes no ledger, source or `.gitignore`, and lays nothing
# new. The key step is `kp.same` for a dependency and `tk.same` for a tool:
# a pin at its own tip, whose checkout there agrees with it, is kept. Each
# fate the first upgrade decides (`a.one`, `t.one`) is carried to the
# second's (`again`), each walk (`w.all`, `tw.all`), then the decision
# (`core`) and the plan.

# the answers the next upgrade reads: `.gitignore` as the last one left it,
# then the same answers
def re(g: String, rs: List<&2, Up.Reply>) -> List<&2, Up.Reply>:
  Up.Reply{Up.Ignore{}, Up.Plain{g}} <> rs

# LAW: a question that is not `.gitignore` is answered past it
law re.heard:
  for +q: Up.Ask
  for g: String
  for rs: List<&2, Up.Reply>
  for ne: {String.eq("ignore", Up.key(q)) == False{} : Bool}
  {Up.heard(re(g, rs), q) == Up.heard(rs, q) : Up.Heard}

def re.heard(q, g, rs, ne):
  nes = Equal.sym(Bool, String.eq("ignore", Up.key(q)), False{}, ne)
  %nes : {Up.look.step(_, Up.Plain{g}, _u => Up.look(rs, Up.key(q))) == Up.heard(rs, q) : Up.Heard}
  {==}

# LAW: what git printed for refs, past `.gitignore`
law re.refs:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +ref: String
  for +what: String
  {Up.printed(re(g, rs), Up.Refs{url, ref}, what) == Up.printed(rs, Up.Refs{url, ref}, what) : Up.Said}

def re.refs(g, rs, url, ref, what):
  Equal.cong(Up.Heard, Up.Said, h => Up.printed.heard(h, Up.Refs{url, ref}, what),
    Up.heard(re(g, rs), Up.Refs{url, ref}), Up.heard(rs, Up.Refs{url, ref}),
    re.heard(Up.Refs{url, ref}, g, rs, {==}))

law re.head:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +what: String
  {Up.printed(re(g, rs), Up.Head{url}, what) == Up.printed(rs, Up.Head{url}, what) : Up.Said}

def re.head(g, rs, url, what):
  Equal.cong(Up.Heard, Up.Said, h => Up.printed.heard(h, Up.Head{url}, what),
    Up.heard(re(g, rs), Up.Head{url}), Up.heard(rs, Up.Head{url}),
    re.heard(Up.Head{url}, g, rs, {==}))

# LAW: the commit a ref names, past `.gitignore`
law re.follow.ask:
  for b: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +ref: String
  {Up.follow.ask(b, re(g, rs), url, ref) == Up.follow.ask(b, rs, url, ref) : Up.Tip}

def re.follow.ask(b, g, rs, url, ref):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.cong(Up.Said, Up.Tip, x => Up.follow.said(x, url, ref),
        Up.printed(re(g, rs), Up.Refs{url, ref}, "ls-remote " ++ url),
        Up.printed(rs, Up.Refs{url, ref}, "ls-remote " ++ url),
        re.refs(g, rs, url, ref, "ls-remote " ++ url))

law re.follow:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +ref: String
  {Up.follow(re(g, rs), url, ref) == Up.follow(rs, url, ref) : Up.Tip}

def re.follow(g, rs, url, ref):
  re.follow.ask(Git.is_rev(ref), g, rs, url, ref)

# LAW: the default branch's tip, past `.gitignore`
law re.forward:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  {Up.forward(re(g, rs), url) == Up.forward(rs, url) : Up.Tip}

def re.forward(g, rs, url):
  Equal.cong(Up.Said, Up.Tip, x => Up.forward.said(x, url),
    Up.printed(re(g, rs), Up.Head{url}, "ls-remote " ++ url),
    Up.printed(rs, Up.Head{url}, "ls-remote " ++ url),
    re.head(g, rs, url, "ls-remote " ++ url))

# LAW: a checkout, past `.gitignore`
law re.checkout:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +rev: String
  for +entry: String
  {Up.checkout(re(g, rs), Up.Tree{url, rev, entry}) == Up.checkout(rs, Up.Tree{url, rev, entry})
    : Up.Co}

def re.checkout(g, rs, url, rev, entry):
  Equal.cong(Up.Heard, Up.Co, h => Up.checkout.heard(h, Up.Tree{url, rev, entry}),
    Up.heard(re(g, rs), Up.Tree{url, rev, entry}), Up.heard(rs, Up.Tree{url, rev, entry}),
    re.heard(Up.Tree{url, rev, entry}, g, rs, {==}))

# LAW: a weighing, past `.gitignore`
law re.weighed:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  for +rev: String
  {Up.weighed(re(g, rs), Up.Weigh{url, rev}) == Up.weighed(rs, Up.Weigh{url, rev}) : Up.Wd}

def re.weighed(g, rs, url, rev):
  Equal.cong(Up.Heard, Up.Wd, h => Up.weighed.heard(h, Up.Weigh{url, rev}),
    Up.heard(re(g, rs), Up.Weigh{url, rev}), Up.heard(rs, Up.Weigh{url, rev}),
    re.heard(Up.Weigh{url, rev}, g, rs, {==}))

# ---------------------------------------------------------------------------
# one dependency, upgraded again

# the tip an aim asks the remote for
def up.tip(am: U.Aim, +rs: List<&2, Up.Reply>, +url: String) -> Up.Tip:
  match am:
    case U.Hold{}:
      Up.TipNo{""}
    case U.Follow{ref}:
      Up.follow(rs, url, ref)
    case U.Forward{}:
      Up.forward(rs, url)

# whether a tip is a commit
def tip.at(t: Up.Tip) -> Bool:
  match t:
    case Up.At{_r, _t, _b}:
      True{}
    case Up.TipWait{_a}:
      False{}
    case Up.TipNo{_w}:
      False{}

# the lines a fate says
def fsays(f: Up.Fate) -> List<&2, String>:
  match f:
    case Up.Became{_d, _o, _n, _p, _m, s, _t}:
      s
    case Up.Waits{_a}:
      []
    case Up.Halts{_w}:
      []

# what the next upgrade makes of a dependency this one left
def again.d(+d: M.Dep, +g: String, +rs: List<&2, Up.Reply>, +only: String, +hub: String) -> Up.Fate:
  Up.dep.one(U.aim(U.chosen(only, M.dep.name(d)), M.source.dep(d)), re(g, rs), only, hub, d)

def again(f: Up.Fate, +g: String, +rs: List<&2, Up.Reply>, +only: String, +hub: String) -> Up.Fate:
  match f:
    case Up.Became{+d, _o, _n, _p, _m, _s, _t}:
      again.d(d, g, rs, only, hub)
    case Up.Waits{+a}:
      Up.Waits{a}
    case Up.Halts{+w}:
      Up.Halts{w}

# LAW: a checkout that agrees with itself
law agree_self:
  for +h: String
  for +nar: String
  for +root: String
  {U.agree(h, h, nar, nar, root, root) == True{} : Bool}

def agree_self(h, nar, root):
  eh = Equal.sym(Bool, String.eq(h, h), True{}, Eq.string_eq_self(h))
  %eh : {U.agree.go(_, String.eq(nar, nar), String.eq(root, root)) == True{} : Bool}
  en = Equal.sym(Bool, String.eq(nar, nar), True{}, Eq.string_eq_self(nar))
  %en : {U.agree.go(True{}, _, String.eq(root, root)) == True{} : Bool}
  Eq.string_eq_self(root)

# LAW: a checkout's own hash is kept as it is: the pin is the walk's
law kept_self:
  for +m: String
  {Up.hash.kept(Up.hash.of(m), m) == Up.hash.of(m) : String}

def kept_self(m):
  eh = Equal.sym(Bool, String.eq(Up.hash.of(m), Up.hash.of(m)), True{},
    Eq.string_eq_self(Up.hash.of(m)))
  %eh : {Up.hash.kept.pick(_, Up.hash.of(m), Up.hash.of(m), m) == Up.hash.of(m) : String}
  {==}

# LAW: and so a pin that is a checkout's own hash agrees with that checkout
law agree_kept_self:
  for +m: String
  for +nar: String
  for +root: String
  {U.agree(Up.hash.of(m), Up.hash.kept(Up.hash.of(m), m), nar, nar, root, root) == True{} : Bool}

def agree_kept_self(m, nar, root):
  ek = Equal.sym(String, Up.hash.kept(Up.hash.of(m), m), Up.hash.of(m), kept_self(m))
  %ek : {U.agree(Up.hash.of(m), _, nar, nar, root, root) == True{} : Bool}
  agree_self(Up.hash.of(m), nar, root)

# LAW: a pin at its own tip, whose checkout there agrees with it, is kept.
# This is the key step of the upgrade's idempotence.
law kp.same:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for es: {String.eq(r, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  for eag: {U.agree(hh, Up.hash.kept(hh, man1), nr, nar1, rt, root1) == True{} : Bool}
  {Up.dep.same(String.eq(r, tip), re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
    tip, tag, br)
    == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.same(String.eq(r, tip), re(g, rs), hub,
        M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br))) : Up.Fate}

def kp.same(g, rs, hub, hn, hh, he, url, r, tg, rt, nr, vd, tip, tag, br, nar1, root1, man1, srcs1, es, eco, eag):
  nes = Equal.sym(Bool, String.eq(r, tip), True{}, es)
  %nes : {Up.dep.same(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br)
    == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.same(_, re(g, rs), hub,
        M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br))) : Up.Fate}
  eco2 = Equal.sym(Up.Co, Up.checkout(re(g, rs), Up.Tree{url, r, he}), Up.Co{nar1, root1, man1, srcs1},
    Equal.trans(Up.Co, Up.checkout(re(g, rs), Up.Tree{url, r, he}), Up.checkout(rs, Up.Tree{url, r, he}),
      Up.Co{nar1, root1, man1, srcs1}, re.checkout(g, rs, url, r, he), eco))
  %eco2 : {Up.dep.kept(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag)
    == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.kept(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, tag)))
    : Up.Fate}
  nag = Equal.sym(Bool, U.agree(hh, Up.hash.kept(hh, man1), nr, nar1, rt, root1), True{}, eag)
  %nag : {Up.dep.verdict(U.judge(True{}, True{}, _, tip, tag), re(g, rs), hub,
      M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, "", Up.hash.kept(hh, man1))
    == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.verdict(U.judge(True{}, True{}, _, tip, tag), re(g, rs), hub,
        M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, tip, "", Up.hash.kept(hh, man1)))) : Up.Fate}
  {==}

# LAW: a tip is not a commit's absence
law tip.clash:
  for +t: Up.Tip
  for +why: String
  for e: {Up.TipNo{why} == t : Up.Tip}
  for a: {tip.at(t) == True{} : Bool}
  {False{} == True{} : Bool}

def tip.clash(t, why, e, a):
  Equal.trans(Bool, False{}, tip.at(t), True{},
    Equal.cong(Up.Tip, Bool, x => tip.at(x), Up.TipNo{why}, t, e), a)

# LAW: the same, once the aim is known
law kp.aim:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  for eag: {U.agree(hh, Up.hash.kept(hh, man1), nr, nar1, rt, root1) == True{} : Bool}
  {Up.dep.one(am, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
    == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.one(am, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})))
    : Up.Fate}

def kp.aim(
  am,
  g,
  rs,
  only,
  hub,
  hn,
  hh,
  he,
  url,
  r,
  tg,
  rt,
  nr,
  vd,
  tip,
  tag,
  br,
  nar1,
  root1,
  man1,
  srcs1,
  et,
  es,
  eco,
  eag
):
  match am:
    case U.Hold{}:
      Eq.bit.absurd(&2, {Up.dep.one(U.Hold{}, re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
        == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
          fsays(Up.dep.one(U.Hold{}, re(g, rs), only, hub,
            M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Fate},
        tip.clash(Up.At{tip, tag, br}, "", et, {==}))
    case U.Follow{+ref}:
      e3 = Equal.sym(Up.Tip, Up.follow(re(g, rs), url, ref), Up.At{tip, tag, br},
        Equal.trans(Up.Tip, Up.follow(re(g, rs), url, ref), Up.follow(rs, url, ref),
          Up.At{tip, tag, br}, re.follow(g, rs, url, ref), et))
      %e3 : {Up.dep.tip(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
        == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
          fsays(Up.dep.tip(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})))
        : Up.Fate}
      kp.same(g, rs, hub, hn, hh, he, url, r, tg, rt, nr, vd, tip, tag, br, nar1, root1, man1, srcs1,
        es, eco, eag)
    case U.Forward{}:
      e3 = Equal.sym(Up.Tip, Up.forward(re(g, rs), url), Up.At{tip, tag, br},
        Equal.trans(Up.Tip, Up.forward(re(g, rs), url), Up.forward(rs, url),
          Up.At{tip, tag, br}, re.forward(g, rs, url), et))
      %e3 : {Up.dep.tip(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
        == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
          fsays(Up.dep.tip(_, re(g, rs), hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})))
        : Up.Fate}
      kp.same(g, rs, hub, hn, hh, he, url, r, tg, rt, nr, vd, tip, tag, br, nar1, root1, man1, srcs1,
        es, eco, eag)

# LAW: the next upgrade keeps a pin that is at the tip its remote names and
# agrees with its checkout there. `ea` says the pin is asked what it was asked
# before, whatever commit, root and narHash it now records.
law kp.again:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +r0: String
  for +rt0: String
  for +nr0: String
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  for eag: {U.agree(hh, Up.hash.kept(hh, man1), nr, nar1, rt, root1) == True{} : Bool}
  {again.d(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, g, rs, only, hub)
    == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(again.d(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}, g, rs, only, hub))) : Up.Fate}

def kp.again(
  am,
  g,
  rs,
  only,
  hub,
  hn,
  hh,
  he,
  url,
  r,
  tg,
  rt,
  nr,
  vd,
  r0,
  rt0,
  nr0,
  tip,
  tag,
  br,
  nar1,
  root1,
  man1,
  srcs1,
  ec,
  ea,
  et,
  es,
  eco,
  eag
):
  nec = Equal.sym(Bool, U.chosen(only, hn), True{}, ec)
  %nec : {Up.dep.one(U.aim(_, M.Git{url, r, tg, rt, nr, vd}), re(g, rs), only, hub,
      M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
    == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.one(U.aim(_, M.Git{url, r, tg, rt, nr, vd}), re(g, rs), only, hub,
        M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Fate}
  nea = Equal.sym(U.Aim, U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), am, ea)
  %nea : {Up.dep.one(_, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})
    == M1.kept(M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}},
      fsays(Up.dep.one(_, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r, tg, rt, nr, vd}})))
    : Up.Fate}
  kp.aim(am, g, rs, only, hub, hn, hh, he, url, r, tg, rt, nr, vd, tip, tag, br, nar1, root1, man1,
    srcs1, et, es, eco, eag)

# LAW: a pin moved to the tip, once the hub has had its word, is kept by the
# next run
law a.hub:
  for hb: Up.Hubbed
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for eco: {Up.checkout(rs, Up.Tree{url, tip, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  {again(Up.dep.hub(hb, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, Up.hash.of(man1), tip, root1, nar1, man1,
    srcs1, br), g, rs, only, hub)
    == M1.still(Up.dep.hub(hb, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, Up.hash.of(man1), tip, root1, nar1,
      man1, srcs1, br),
      fsays(again(Up.dep.hub(hb, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, Up.hash.of(man1), tip, root1,
        nar1, man1, srcs1, br), g, rs, only, hub))) : Up.Fate}

def a.hub(
  hb,
  g,
  rs,
  only,
  hub,
  hn,
  _hh,
  he,
  url,
  r0,
  tg,
  rt0,
  nr0,
  vd,
  am,
  tip,
  tag,
  br,
  nar1,
  root1,
  man1,
  srcs1,
  ec,
  ea,
  et,
  eco
):
  match hb:
    case Up.Clear{}:
      kp.again(am, g, rs, only, hub, hn, Up.hash.of(man1), he, url, tip, tg, root1, nar1, vd, r0, rt0,
        nr0, tip, tag, br, nar1, root1, man1, srcs1, ec, ea, et, Eq.string_eq_self(tip), eco,
        agree_kept_self(man1, nar1, root1))
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

# LAW: a pin moved to the tip, once its checkout is in
law a.adv:
  for co: Up.Co
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for eco: {Up.checkout(rs, Up.Tree{url, tip, he}) == co : Up.Co}
  {again(Up.dep.advance(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, br), g, rs, only, hub)
    == M1.still(Up.dep.advance(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, br),
      fsays(again(Up.dep.advance(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, br), g, rs,
        only, hub))) : Up.Fate}

def a.adv(co, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et, eco):
  match co:
    case Up.Co{+nar1, +root1, +man1, +srcs1}:
      a.hub(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(man1)}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd,
        am, tip, tag, br, nar1, root1,
        man1, srcs1, ec, ea, et, eco)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: a tip that is another commit, once ancestry is in
law a.onward:
  for asc: Up.Asc
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  {again(Up.dep.onward(asc, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs, only,
    hub)
    == M1.still(Up.dep.onward(asc, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br),
      fsays(again(Up.dep.onward(asc, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g,
        rs, only, hub))) : Up.Fate}

def a.onward(asc, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et):
  match asc:
    case Up.Asc{yes}:
      match yes:
        case True{}:
          a.adv(Up.checkout(rs, Up.Tree{url, tip, he}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am,
            tip, tag, br, ec, ea, et, {==})
        case False{}:
          {==}
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the pin's own commit, judged by whether its checkout agrees
law a.agree:
  for ag: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for +nar1: String
  for +root1: String
  for +man1: String
  for +srcs1: List<&2, String>
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r0, he}) == Up.Co{nar1, root1, man1, srcs1} : Up.Co}
  for eag: {U.agree(hh, Up.hash.kept(hh, man1), nr0, nar1, rt0, root1) == ag : Bool}
  {again(Up.dep.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0,
    vd}}, tip, "", Up.hash.kept(hh, man1)), g, rs, only, hub)
    == M1.still(Up.dep.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0,
      nr0, vd}}, tip, "", Up.hash.kept(hh, man1)),
      fsays(again(Up.dep.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg,
        rt0, nr0, vd}}, tip, "", Up.hash.kept(hh, man1)), g, rs, only, hub))) : Up.Fate}

def a.agree(
  ag,
  g,
  rs,
  only,
  hub,
  hn,
  hh,
  he,
  url,
  r0,
  tg,
  rt0,
  nr0,
  vd,
  am,
  tip,
  tag,
  br,
  nar1,
  root1,
  man1,
  srcs1,
  ec,
  ea,
  et,
  es,
  eco,
  eag
):
  match ag:
    case True{}:
      kp.again(am, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, r0, rt0, nr0, tip, tag, br,
        nar1, root1, man1, srcs1, ec, ea, et, es, eco, eag)
    case False{}:
      {==}

# LAW: the pin's own commit, once its checkout is in
law a.kept:
  for co: Up.Co
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == True{} : Bool}
  for eco: {Up.checkout(rs, Up.Tree{url, r0, he}) == co : Up.Co}
  {again(Up.dep.kept(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag), g, rs, only, hub)
    == M1.still(Up.dep.kept(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag),
      fsays(again(Up.dep.kept(co, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag), g, rs,
        only, hub))) : Up.Fate}

def a.kept(co, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et, es, eco):
  match co:
    case Up.Co{+nar1, +root1, +man1, +srcs1}:
      a.agree(U.agree(hh, Up.hash.kept(hh, man1), nr0, nar1, rt0, root1), g, rs, only, hub, hn, hh, he,
        url, r0, tg, rt0, nr0, vd, am, tip, tag, br, nar1, root1,
        man1, srcs1, ec, ea, et, es, eco, {==})
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

# LAW: the tip against the pin
law a.same:
  for s: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == s : Bool}
  {again(Up.dep.same(s, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs, only, hub)
    == M1.still(Up.dep.same(s, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br),
      fsays(again(Up.dep.same(s, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs,
        only, hub))) : Up.Fate}

def a.same(s, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et, es):
  match s:
    case True{}:
      a.kept(Up.checkout(rs, Up.Tree{url, r0, he}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip,
        tag, br, ec, ea, et, es, {==})
    case False{}:
      a.onward(Up.onward(rs, Up.Above{url, r0, tip}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am,
        tip, tag, br, ec, ea, et)

# LAW: whatever tip the remote named
law a.tip:
  for t: Up.Tip
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == t : Up.Tip}
  {again(Up.dep.tip(t, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only, hub)
    == M1.still(Up.dep.tip(t, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}),
      fsays(again(Up.dep.tip(t, rs, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only,
        hub))) : Up.Fate}

def a.tip(t, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, ec, ea, et):
  match t:
    case Up.At{+tip, +tag, +br}:
      a.same(String.eq(r0, tip), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea,
        et, {==})
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: a pin from a repository that is asked about, whatever it is asked
law a.git:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, hn) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  {again(Up.dep.one(am, rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only, hub)
    == M1.still(Up.dep.one(am, rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}),
      fsays(again(Up.dep.one(am, rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only,
        hub))) : Up.Fate}

def a.git(am, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, ec, ea):
  match am:
    case U.Hold{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), True{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Git{url, r0, tg, rt0, nr0, vd}), re(g, rs), only, hub, M.Dep{hn, hh, he,
        M.Git{url, r0, tg, rt0, nr0, vd}})
        == M1.kept(M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, fsays(Up.dep.one(U.aim(_, M.Git{url, r0, tg,
            rt0,
          nr0, vd}), re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Fate}
      nea = Equal.sym(U.Aim, U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), U.Hold{}, ea)
      %nea : {Up.dep.one(_, re(g, rs), only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}})
        == M1.kept(M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, fsays(Up.dep.one(_, re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Fate}
      {==}
    case U.Follow{+ref}:
      a.tip(Up.follow(rs, url, ref), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, U.Follow{ref}, ec, ea,
        {==})
    case U.Forward{}:
      a.tip(Up.forward(rs, url), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, U.Forward{}, ec, ea, {==})

# LAW: a pin from a repository, asked about or not
law a.gsel:
  for sel: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, hn) == sel : Bool}
  {again(Up.dep.one(U.aim(sel, M.Git{url, r0, tg, rt0, nr0, vd}), rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0, tg,
    rt0, nr0, vd}}), g, rs, only, hub)
    == M1.still(Up.dep.one(U.aim(sel, M.Git{url, r0, tg, rt0, nr0, vd}), rs, only, hub, M.Dep{hn, hh, he, M.Git{url, r0,
      tg, rt0, nr0, vd}}),
      fsays(again(Up.dep.one(U.aim(sel, M.Git{url, r0, tg, rt0, nr0, vd}), rs, only, hub, M.Dep{hn, hh, he, M.Git{url,
        r0, tg, rt0, nr0, vd}}), g, rs, only, hub))) : Up.Fate}

def a.gsel(sel, g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, ec):
  match sel:
    case True{}:
      a.git(U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd,
        ec, {==})
    case False{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), False{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Git{url, r0, tg, rt0, nr0, vd}), re(g, rs), only, hub, M.Dep{hn, hh, he,
        M.Git{url, r0, tg, rt0, nr0, vd}})
        == M1.kept(M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}, fsays(Up.dep.one(U.aim(_, M.Git{url, r0, tg,
            rt0,
          nr0, vd}), re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Fate}
      {==}

# LAW: a hub pin is held, chosen or not, and held again by the next run
law a.hubsel:
  for sel: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +hv: String
  for ec: {U.chosen(only, hn) == sel : Bool}
  {again(Up.dep.one(U.aim(sel, M.Hub{hv}), rs, only, hub, M.Dep{hn, hh, he, M.Hub{hv}}), g, rs, only, hub)
    == M1.still(Up.dep.one(U.aim(sel, M.Hub{hv}), rs, only, hub, M.Dep{hn, hh, he, M.Hub{hv}}),
      fsays(again(Up.dep.one(U.aim(sel, M.Hub{hv}), rs, only, hub, M.Dep{hn, hh, he, M.Hub{hv}}), g, rs,
        only, hub))) : Up.Fate}

def a.hubsel(sel, g, rs, only, hub, hn, hh, he, hv, ec):
  match sel:
    case True{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), True{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Hub{hv}), re(g, rs), only, hub, M.Dep{hn, hh, he, M.Hub{hv}})
        == M1.kept(M.Dep{hn, hh, he, M.Hub{hv}}, fsays(Up.dep.one(U.aim(_, M.Hub{hv}), re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Hub{hv}}))) : Up.Fate}
      {==}
    case False{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), False{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Hub{hv}), re(g, rs), only, hub, M.Dep{hn, hh, he, M.Hub{hv}})
        == M1.kept(M.Dep{hn, hh, he, M.Hub{hv}}, fsays(Up.dep.one(U.aim(_, M.Hub{hv}), re(g, rs), only, hub,
          M.Dep{hn, hh, he, M.Hub{hv}}))) : Up.Fate}
      {==}

# LAW: and so is a workspace member's, as a hub source is
law a.memsel:
  for sel: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +hn: String
  for +hh: String
  for +he: String
  for +mp: String
  for +mn: String
  for ec: {U.chosen(only, hn) == sel : Bool}
  {again(Up.dep.one(U.aim(sel, M.Member{mp, mn}), rs, only, hub, M.Dep{hn, hh, he, M.Member{mp, mn}}), g, rs, only, hub)
    == M1.still(Up.dep.one(U.aim(sel, M.Member{mp, mn}), rs, only, hub, M.Dep{hn, hh, he, M.Member{mp, mn}}),
      fsays(again(Up.dep.one(U.aim(sel, M.Member{mp, mn}), rs, only, hub, M.Dep{hn, hh, he, M.Member{mp, mn}}), g, rs,
        only, hub))) : Up.Fate}

def a.memsel(sel, g, rs, only, hub, hn, hh, he, mp, mn, ec):
  match sel:
    case True{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), True{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Member{mp, mn}), re(g, rs), only, hub, M.Dep{hn, hh, he, M.Member{mp, mn}})
        == M1.kept(M.Dep{hn, hh, he, M.Member{mp, mn}}, fsays(Up.dep.one(U.aim(_, M.Member{mp, mn}), re(g, rs), only,
            hub,
          M.Dep{hn, hh, he, M.Member{mp, mn}}))) : Up.Fate}
      {==}
    case False{}:
      nec = Equal.sym(Bool, U.chosen(only, hn), False{}, ec)
      %nec : {Up.dep.one(U.aim(_, M.Member{mp, mn}), re(g, rs), only, hub, M.Dep{hn, hh, he, M.Member{mp, mn}})
        == M1.kept(M.Dep{hn, hh, he, M.Member{mp, mn}}, fsays(Up.dep.one(U.aim(_, M.Member{mp, mn}), re(g, rs), only,
            hub,
          M.Dep{hn, hh, he, M.Member{mp, mn}}))) : Up.Fate}
      {==}

# LAW: whatever the upgrade makes of a dependency, the next upgrade, against
# the same remote, keeps the pin it left, or stops as it did
law a.one:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +d: M.Dep
  {again(Up.dep.one(U.aim(U.chosen(only, M.dep.name(d)), M.source.dep(d)), rs, only, hub, d), g, rs,
    only, hub)
    == M1.still(Up.dep.one(U.aim(U.chosen(only, M.dep.name(d)), M.source.dep(d)), rs, only, hub, d),
      fsays(again(Up.dep.one(U.aim(U.chosen(only, M.dep.name(d)), M.source.dep(d)), rs, only, hub, d),
        g, rs, only, hub))) : Up.Fate}

def a.one(g, rs, only, hub, d):
  match d:
    case M.Dep{+hn, +hh, +he, src}:
      match src:
        case M.Hub{hv}:
          a.hubsel(U.chosen(only, hn), g, rs, only, hub, hn, hh, he, hv, {==})
        case M.Git{+url, +r0, +tg, +rt0, +nr0, +vd}:
          a.gsel(U.chosen(only, hn), g, rs, only, hub, hn, hh, he, url, r0, tg, rt0, nr0, vd, {==})
        case M.Member{mp, mn}:
          a.memsel(U.chosen(only, hn), g, rs, only, hub, hn, hh, he, mp, mn, {==})

law moved_back:
  for +dep: M.Dep
  for +hash: String
  for +rev: String
  for +root: String
  for +nar: String
  for manifest: String
  for srcs: List<&2, String>
  for +branch: String
  {M1.back(Up.dep.moved(dep, hash, rev, root, nar, manifest, srcs, branch), dep) == dep : M.Dep}

def moved_back(_dep, _hash, _rev, _root, _nar, _manifest, _srcs, _branch):
  {==}

law hub_back:
  for hubbed: Up.Hubbed
  for +dep: M.Dep
  for +hash: String
  for +rev: String
  for +root: String
  for +nar: String
  for manifest: String
  for srcs: List<&2, String>
  for +branch: String
  {M1.back(Up.dep.hub(hubbed, dep, hash, rev, root, nar, manifest, srcs, branch), dep) == dep : M.Dep}

def hub_back(hubbed, dep, hash, rev, root, nar, manifest, srcs, branch):
  match hubbed:
    case Up.Clear{}:
      moved_back(dep, hash, rev, root, nar, manifest, srcs, branch)
    case Up.Clash{}:
      {==}
    case Up.HubWait{_ask}:
      {==}
    case Up.HubNo{_why}:
      {==}

law advance_back:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +rev: String
  for +branch: String
  {M1.back(Up.dep.advance(co, rs, hub, dep, rev, branch), dep) == dep : M.Dep}

def advance_back(co, rs, hub, dep, rev, branch):
  match co:
    case Up.Co{nar, root, +manifest, srcs}:
      hub_back(Up.hubbed(rs, Up.HubHas{hub, Up.hash.of(manifest)}), dep, Up.hash.of(manifest),
        rev, root, nar, manifest, srcs, branch)
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

law verdict_back:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +branch: String
  for +seen: String
  {M1.back(Up.dep.verdict(verdict, rs, hub, dep, tip, branch, seen), dep) == dep : M.Dep}

def verdict_back(verdict, rs, hub, dep, _tip, branch, _seen):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, _tag}:
      advance_back(Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(dep)), rev, M.dep.entry(dep)}),
        rs, hub, dep, rev, branch)

law kept_back:
  for co: Up.Co
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  {M1.back(Up.dep.kept(co, rs, hub, dep, tip, tag), dep) == dep : M.Dep}

def kept_back(co, rs, hub, dep, tip, tag):
  match co:
    case Up.Co{nar, root, +manifest, _srcs}:
      verdict_back(U.judge(True{}, True{},
        U.agree(M.dep.hash(dep), Up.hash.kept(M.dep.hash(dep), manifest), M.source.nar(M.source.dep(dep)), nar,
          M.source.root(M.source.dep(dep)), root), tip, tag), rs, hub, dep, tip, "",
        Up.hash.kept(M.dep.hash(dep), manifest))
    case Up.CoWait{_ask}:
      {==}
    case Up.CoNo{_why}:
      {==}

law onward_back:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  for +branch: String
  {M1.back(Up.dep.onward(asc, rs, hub, dep, tip, tag, branch), dep) == dep : M.Dep}

def onward_back(asc, rs, hub, dep, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      verdict_back(U.judge(False{}, yes, False{}, tip, tag), rs, hub, dep, tip, branch, "")
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law same_back:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  for +tip: String
  for +tag: String
  for +branch: String
  {M1.back(Up.dep.same(same, rs, hub, dep, tip, tag, branch), dep) == dep : M.Dep}

def same_back(same, rs, hub, dep, tip, tag, branch):
  match same:
    case True{}:
      kept_back(Up.checkout(rs, Up.Tree{M.source.url(M.source.dep(dep)),
        M.source.rev(M.source.dep(dep)), M.dep.entry(dep)}), rs, hub, dep, tip, tag)
    case False{}:
      onward_back(Up.onward(rs, Up.Above{M.source.url(M.source.dep(dep)),
        M.source.rev(M.source.dep(dep)), tip}), rs, hub, dep, tip, tag, branch)

law tip_back:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +hub: String
  for +dep: M.Dep
  {M1.back(Up.dep.tip(tip, rs, hub, dep), dep) == dep : M.Dep}

def tip_back(tip, rs, hub, dep):
  match tip:
    case Up.At{+rev, tag, branch}:
      same_back(String.eq(M.source.rev(M.source.dep(dep)), rev), rs, hub, dep, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: whatever the upgrade makes of one dependency, what it leaves in the
# ledger has the dependency's name
law one_back:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +dep: M.Dep
  {M1.back(Up.dep.one(aim, rs, only, hub, dep), dep) == dep : M.Dep}

def one_back(aim, rs, _only, hub, dep):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      tip_back(Up.follow(rs, M.source.url(M.source.dep(dep)), ref), rs, hub, dep)
    case U.Forward{}:
      tip_back(Up.forward(rs, M.source.url(M.source.dep(dep))), rs, hub, dep)

# the tool pin a pin leaves when it says it did not move, else the one it had
def tback(p: Up.Pinned, +t: M.Cli) -> M.Cli:
  match p:
    case Up.Pinned{t2, m, _s}:
      Bool.pick(M.Cli, m, t, t2)
    case Up.PinWait{_a}:
      t
    case Up.PinHalt{_w}:
      t

law tpin_tback:
  for short: Bool
  for +tool: M.Cli
  for +rev: String
  for +tag: String
  for +nar: String
  for says: List<&2, String>
  {tback(Up.tool.pin(short, tool, rev, tag, nar, says), tool) == tool : M.Cli}

def tpin_tback(short, _tool, _rev, _tag, _nar, _says):
  match short:
    case True{}:
      {==}
    case False{}:
      {==}

law weighed_tback:
  for wd: Up.Wd
  for +tool: M.Cli
  for +rev: String
  for +tag: String
  for says: List<&2, String>
  {tback(Up.tool.weighed(wd, tool, rev, tag, says), tool) == tool : M.Cli}

def weighed_tback(wd, tool, rev, tag, says):
  match wd:
    case Up.Wd{+nar}:
      tpin_tback(Bool.or(String.is_empty(rev), String.is_empty(nar)), tool, rev, tag, nar, says)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law resolved_tback:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +ref: String
  {tback(Up.tool.resolved(tip, rs, tool, ref), tool) == tool : M.Cli}

def resolved_tback(tip, rs, tool, ref):
  match tip:
    case Up.At{+rev, _tag, _branch}:
      weighed_tback(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, ref, [])
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law named_tback:
  for named: Up.Named
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +url: String
  {tback(Up.tool.named(named, rs, tool, url), tool) == tool : M.Cli}

def named_tback(named, rs, tool, url):
  match named:
    case Up.Named{+ref}:
      resolved_tback(Up.follow(rs, url, ref), rs, tool, ref)
    case Up.NamedWait{_ask}:
      {==}
    case Up.NamedNo{_why}:
      {==}

law tverdict_tback:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +branch: String
  {tback(Up.tool.verdict(verdict, rs, tool, tip, branch), tool) == tool : M.Cli}

def tverdict_tback(verdict, rs, tool, _tip, branch):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, _tag}:
      weighed_tback(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, "",
        [Up.say.move(M.tool.name(tool), M.source.rev(M.tool.source(tool)), rev, branch)])

law tkept_nar_tback:
  for fill: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  for +nar: String
  {tback(Up.tool.kept.nar(fill, rs, tool, tip, tag, nar), tool) == tool : M.Cli}

def tkept_nar_tback(fill, rs, tool, tip, tag, nar):
  match fill:
    case True{}:
      tpin_tback(Bool.or(String.is_empty(tip), String.is_empty(nar)), tool, tip, "", nar, [])
    case False{}:
      tverdict_tback(U.judge(True{}, True{}, String.eq(M.source.nar(M.tool.source(tool)), nar), tip, tag),
        rs, tool, tip, "")

law tkept_tback:
  for wd: Up.Wd
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  {tback(Up.tool.kept(wd, rs, tool, tip, tag), tool) == tool : M.Cli}

def tkept_tback(wd, rs, tool, tip, tag):
  match wd:
    case Up.Wd{+nar}:
      tkept_nar_tback(String.is_empty(M.source.nar(M.tool.source(tool))), rs, tool, tip, tag, nar)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law tonward_tback:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  for +branch: String
  {tback(Up.tool.onward(asc, rs, tool, tip, tag, branch), tool) == tool : M.Cli}

def tonward_tback(asc, rs, tool, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      tverdict_tback(U.judge(False{}, yes, False{}, tip, tag), rs, tool, tip, branch)
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law tsame_tback:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  for +branch: String
  {tback(Up.tool.same(same, rs, tool, tip, tag, branch), tool) == tool : M.Cli}

def tsame_tback(same, rs, tool, tip, tag, branch):
  match same:
    case True{}:
      tkept_tback(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool))}), rs, tool, tip, tag)
    case False{}:
      tonward_tback(Up.onward(rs, Up.Above{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool)), tip}), rs, tool, tip, tag, branch)

law ttip_tback:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {tback(Up.tool.tip(tip, rs, tool), tool) == tool : M.Cli}

def ttip_tback(tip, rs, tool):
  match tip:
    case Up.At{+rev, tag, branch}:
      tsame_tback(String.eq(M.source.rev(M.tool.source(tool)), rev), rs, tool, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law taim_tback:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {tback(Up.tool.aim(aim, rs, tool), tool) == tool : M.Cli}

def taim_tback(aim, rs, tool):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      ttip_tback(Up.follow(rs, M.source.url(M.tool.source(tool)), ref), rs, tool)
    case U.Forward{}:
      ttip_tback(Up.forward(rs, M.source.url(M.tool.source(tool))), rs, tool)

law fill_tback:
  for no_rev: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {tback(Up.tool.fill(no_rev, rs, tool), tool) == tool : M.Cli}

def fill_tback(no_rev, rs, tool):
  match no_rev:
    case True{}:
      named_tback(Up.tool.ref(String.is_empty(M.source.tag(M.tool.source(tool))), rs,
        M.source.url(M.tool.source(tool)), M.source.tag(M.tool.source(tool))), rs, tool,
        M.source.url(M.tool.source(tool)))
    case False{}:
      taim_tback(U.aim(True{}, M.tool.source(tool)), rs, tool)

law short_tback:
  for short: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {tback(Up.tool.short(short, rs, tool), tool) == tool : M.Cli}

def short_tback(short, rs, tool):
  match short:
    case True{}:
      fill_tback(String.is_empty(M.source.rev(M.tool.source(tool))), rs, tool)
    case False{}:
      taim_tback(U.aim(True{}, M.tool.source(tool)), rs, tool)

law git_tback:
  for git: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {tback(Up.tool.git(git, rs, tool), tool) == tool : M.Cli}

def git_tback(git, rs, tool):
  match git:
    case False{}:
      {==}
    case True{}:
      short_tback(Bool.or(String.is_empty(M.source.rev(M.tool.source(tool))),
        String.is_empty(M.source.nar(M.tool.source(tool)))), rs, tool)

# LAW: whatever the upgrade makes of one tool, what it leaves in the ledger has
# the tool's name
law sel_tback:
  for sel: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {tback(Up.tool.sel(sel, rs, tool), tool) == tool : M.Cli}

def sel_tback(sel, rs, tool):
  match sel:
    case False{}:
      {==}
    case True{}:
      git_tback(M.source.is_git(M.tool.source(tool)), rs, tool)

# ---------------------------------------------------------------------------
# one tool, upgraded again

# a tool pin kept as it is, with the lines it says
def pkept(t: M.Cli, s: List<&2, String>) -> Up.Pinned:
  Up.Pinned{t, False{}, s}

# the lines a tool's fate says
def psays(p: Up.Pinned) -> List<&2, String>:
  match p:
    case Up.Pinned{_t, _m, s}:
      s
    case Up.PinWait{_a}:
      []
    case Up.PinHalt{_w}:
      []

# what the next upgrade makes of a tool pin this one left
def again_t.t(+t: M.Cli, +g: String, +rs: List<&2, Up.Reply>, +only: String) -> Up.Pinned:
  Up.tool.sel(U.chosen(only, M.tool.name(t)), re(g, rs), t)

def again_t(p: Up.Pinned, +g: String, +rs: List<&2, Up.Reply>, +only: String) -> Up.Pinned:
  match p:
    case Up.Pinned{+t, _m, _s}:
      again_t.t(t, g, rs, only)
    case Up.PinWait{a}:
      Up.PinWait{a}
    case Up.PinHalt{w}:
      Up.PinHalt{w}

# a tool's fate with the pin it left kept, saying the lines given
def still_t(p: Up.Pinned, s: List<&2, String>) -> Up.Pinned:
  match p:
    case Up.Pinned{t, _m, _s}:
      pkept(t, s)
    case Up.PinWait{a}:
      Up.PinWait{a}
    case Up.PinHalt{w}:
      Up.PinHalt{w}

# LAW: an `or` that answered False answered False on its left
law or_false_l:
  for a: Bool
  for +c: Bool
  for e: {Bool.or(a, c) == False{} : Bool}
  {a == False{} : Bool}

def or_false_l(a, _c, e):
  match a:
    case True{}:
      Eq.bit.absurd2(&2, {True{} == False{} : Bool}, e)
    case False{}:
      {==}

# LAW: and on its right
law or_false_r:
  for a: Bool
  for +c: Bool
  for e: {Bool.or(a, c) == False{} : Bool}
  {c == False{} : Bool}

def or_false_r(a, c, e):
  match a:
    case True{}:
      Eq.bit.absurd2(&2, {c == False{} : Bool}, e)
    case False{}:
      e

# LAW: a pin with a commit is upgraded as a full pin is, however short it is
law short_aim:
  for x: Bool
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for hr: {String.is_empty(r) == False{} : Bool}
  {Up.tool.short(x, rs, M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    == Up.tool.aim(U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}), rs, M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    : Up.Pinned}

def short_aim(x, rs, n, e, b, url, r, tg, rt, nr, vd, hr):
  match x:
    case False{}:
      {==}
    case True{}:
      nhr = Equal.sym(Bool, String.is_empty(r), False{}, hr)
      %nhr : {Up.tool.fill(_, rs, M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
        == Up.tool.aim(U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}), rs,
          M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}) : Up.Pinned}
      {==}

# LAW: a tool pin at its own tip, weighed there to its own NAR hash, is kept
law tk.same:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for +hn: {String.is_empty(nr) == False{} : Bool}
  for es: {String.eq(r, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r}) == Up.Wd{nw} : Up.Wd}
  for eqn: {String.eq(nr, nw) == True{} : Bool}
  {Up.tool.same(String.eq(r, tip), re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br)
    == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.same(String.eq(r, tip), re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
        tip, tag, br))) : Up.Pinned}

def tk.same(g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, es, ewd, eqn):
  nes = Equal.sym(Bool, String.eq(r, tip), True{}, es)
  %nes : {Up.tool.same(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br)
    == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.same(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, br)))
    : Up.Pinned}
  ew = Equal.sym(Up.Wd, Up.weighed(re(g, rs), Up.Weigh{url, r}), Up.Wd{nw},
    Equal.trans(Up.Wd, Up.weighed(re(g, rs), Up.Weigh{url, r}), Up.weighed(rs, Up.Weigh{url, r}),
      Up.Wd{nw}, re.weighed(g, rs, url, r), ewd))
  %ew : {Up.tool.kept(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag)
    == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.kept(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag)))
    : Up.Pinned}
  nhn = Equal.sym(Bool, String.is_empty(nr), False{}, hn)
  %nhn : {Up.tool.kept.nar(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, nw)
    == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.kept.nar(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, tag, nw)))
    : Up.Pinned}
  neq = Equal.sym(Bool, String.eq(nr, nw), True{}, eqn)
  %neq : {Up.tool.verdict(U.judge(True{}, True{}, _, tip, tag), re(g, rs),
      M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, "")
    == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.verdict(U.judge(True{}, True{}, _, tip, tag), re(g, rs),
        M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, tip, ""))) : Up.Pinned}
  {==}

# LAW: the same, once the aim is known
law tk.aim:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for +hn: {String.is_empty(nr) == False{} : Bool}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r}) == Up.Wd{nw} : Up.Wd}
  for eqn: {String.eq(nr, nw) == True{} : Bool}
  {Up.tool.aim(am, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.aim(am, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}

def tk.aim(am, g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, et, es, ewd, eqn):
  match am:
    case U.Hold{}:
      Eq.bit.absurd(&2, {Up.tool.aim(U.Hold{}, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
        == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
          psays(Up.tool.aim(U.Hold{}, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})))
        : Up.Pinned}, tip.clash(Up.At{tip, tag, br}, "", et, {==}))
    case U.Follow{+ref}:
      e3 = Equal.sym(Up.Tip, Up.follow(re(g, rs), url, ref), Up.At{tip, tag, br},
        Equal.trans(Up.Tip, Up.follow(re(g, rs), url, ref), Up.follow(rs, url, ref),
          Up.At{tip, tag, br}, re.follow(g, rs, url, ref), et))
      %e3 : {Up.tool.tip(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
        == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
          psays(Up.tool.tip(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}
      tk.same(g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, es, ewd, eqn)
    case U.Forward{}:
      e3 = Equal.sym(Up.Tip, Up.forward(re(g, rs), url), Up.At{tip, tag, br},
        Equal.trans(Up.Tip, Up.forward(re(g, rs), url), Up.forward(rs, url),
          Up.At{tip, tag, br}, re.forward(g, rs, url), et))
      %e3 : {Up.tool.tip(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
        == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
          psays(Up.tool.tip(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}
      tk.same(g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, es, ewd, eqn)

# LAW: the next upgrade keeps a tool pin that is at the tip its remote names,
# whose NAR hash is the one the weighing there gave
law tk.again:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r: String
  for +tg: String
  for +rt: String
  for +nr: String
  for +vd: Bool
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr: {String.is_empty(r) == False{} : Bool}
  for +hn: {String.is_empty(nr) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r}) == Up.Wd{nw} : Up.Wd}
  for eqn: {String.eq(nr, nw) == True{} : Bool}
  {again_t.t(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, g, rs, only)
    == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(again_t.t(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, g, rs, only))) : Up.Pinned}

def tk.again(am, g, rs, only, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, ec, hr, hn, ea, et, es, ewd, eqn):
  nec = Equal.sym(Bool, U.chosen(only, n), True{}, ec)
  %nec : {Up.tool.sel(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.sel(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}
  sa = Equal.sym(Up.Pinned,
    Up.tool.short(Bool.or(String.is_empty(r), String.is_empty(nr)), re(g, rs),
      M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}),
    Up.tool.aim(U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}), re(g, rs),
      M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}),
    short_aim(Bool.or(String.is_empty(r), String.is_empty(nr)), re(g, rs), n, e, b, url, r, tg, rt,
      nr, vd, hr))
  %sa : {_ == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}, psays(_)) : Up.Pinned}
  nea = Equal.sym(U.Aim, U.aim(True{}, M.Git{url, r, tg, rt, nr, vd}), am, ea)
  %nea : {Up.tool.aim(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}})
    == pkept(M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}},
      psays(Up.tool.aim(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r, tg, rt, nr, vd}}))) : Up.Pinned}
  tk.aim(am, g, rs, n, e, b, url, r, tg, rt, nr, vd, tip, tag, br, nw, hn, et, es, ewd, eqn)

# LAW: a commit weighed and written into the pin is kept by the next run
law t.pin:
  for gd: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +tagarg: String
  for says: List<&2, String>
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, Bool.pick(String, String.is_empty(tagarg), tg, tagarg), rt0, nr0,
      vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for ewd: {Up.weighed(rs, Up.Weigh{url, tip}) == Up.Wd{nw} : Up.Wd}
  for +egd: {Bool.or(String.is_empty(tip), String.is_empty(nw)) == gd : Bool}
  {again_t(Up.tool.pin(gd, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, nw, says), g, rs, only)
    == still_t(Up.tool.pin(gd, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, nw, says),
      psays(again_t(Up.tool.pin(gd, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, nw, says), g, rs,
        only))) : Up.Pinned}

def t.pin(
  gd,
  g,
  rs,
  only,
  n,
  e,
  b,
  url,
  _r0,
  tg,
  rt0,
  _nr0,
  _vd,
  tagarg,
  _says,
  am,
  tip,
  tag,
  br,
  nw,
  ec,
  ea,
  et,
  ewd,
  egd
):
  match gd:
    case True{}:
      {==}
    case False{}:
      tk.again(am, g, rs, only, n, e, b, url, tip, Bool.pick(String, String.is_empty(tagarg), tg, tagarg),
        M.root.or(rt0), nw, False{}, tip, tag, br, nw, ec,
        or_false_l(String.is_empty(tip), String.is_empty(nw), egd),
        or_false_r(String.is_empty(tip), String.is_empty(nw), egd),
        ea, et, Eq.string_eq_self(tip), ewd, Eq.string_eq_self(nw))

# LAW: a commit, once it is weighed
law t.weighed:
  for wd: Up.Wd
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +tagarg: String
  for says: List<&2, String>
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, Bool.pick(String, String.is_empty(tagarg), tg, tagarg), rt0, nr0,
      vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for ewd: {Up.weighed(rs, Up.Weigh{url, tip}) == wd : Up.Wd}
  {again_t(Up.tool.weighed(wd, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, says), g, rs, only)
    == still_t(Up.tool.weighed(wd, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, says),
      psays(again_t(Up.tool.weighed(wd, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tagarg, says), g, rs,
        only))) : Up.Pinned}

def t.weighed(wd, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, tagarg, says, am, tip, tag, br, ec, ea, et, ewd):
  match wd:
    case Up.Wd{+nw}:
      t.pin(Bool.or(String.is_empty(tip), String.is_empty(nw)), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd,
        tagarg, says, am, tip, tag, br, nw,
        ec, ea, et, ewd, {==})
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

# LAW: the pin's own commit, judged by its NAR hash
law t.tagree:
  for ag: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for +nw: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for +hn0: {String.is_empty(nr0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r0}) == Up.Wd{nw} : Up.Wd}
  for eag: {String.eq(nr0, nw) == ag : Bool}
  {again_t(Up.tool.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0,
    vd}}, tip, ""), g, rs, only)
    == still_t(Up.tool.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0,
      vd}}, tip, ""),
      psays(again_t(Up.tool.verdict(U.judge(True{}, True{}, ag, tip, tag), rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0,
        nr0, vd}}, tip, ""), g, rs, only))) : Up.Pinned}

def t.tagree(
  ag,
  g,
  rs,
  only,
  n,
  e,
  b,
  url,
  r0,
  tg,
  rt0,
  nr0,
  vd,
  am,
  tip,
  tag,
  br,
  nw,
  ec,
  hr0,
  hn0,
  ea,
  et,
  es,
  ewd,
  eag
):
  match ag:
    case True{}:
      tk.again(am, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, tip, tag, br, nw, ec, hr0, hn0, ea,
        et, es, ewd, eag)
    case False{}:
      {==}

# LAW: the pin's own commit weighed: filled when it had no NAR hash, else
# judged
law t.knar:
  for f: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +nw: String
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for +es: {String.eq(r0, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r0}) == Up.Wd{nw} : Up.Wd}
  for ef: {String.is_empty(nr0) == f : Bool}
  {again_t(Up.tool.kept.nar(f, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, nw), g, rs, only)
    == still_t(Up.tool.kept.nar(f, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, nw),
      psays(again_t(Up.tool.kept.nar(f, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, nw), g, rs,
        only))) : Up.Pinned}

def t.knar(f, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, nw, am, tip, tag, br, ec, hr0, ea, et, es, ewd, ef):
  match f:
    case True{}:
      rt = Str.string_eq_true(r0, tip, es)
      ewd2 = Equal.trans(Up.Wd, Up.weighed(rs, Up.Weigh{url, tip}), Up.weighed(rs, Up.Weigh{url, r0}),
        Up.Wd{nw},
        Equal.cong(String, Up.Wd, x => Up.weighed(rs, Up.Weigh{url, x}), tip, r0,
          Equal.sym(String, r0, tip, rt)),
        ewd)
      t.pin(Bool.or(String.is_empty(tip), String.is_empty(nw)), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, "",
        [], am, tip, tag, br, nw, ec,
        ea, et, ewd2, {==})
    case False{}:
      t.tagree(String.eq(nr0, nw), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, nw, ec, hr0, ef,
        ea, et, es, ewd, {==})

# LAW: the pin's own commit, once it is weighed
law t.kept:
  for wd: Up.Wd
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for +es: {String.eq(r0, tip) == True{} : Bool}
  for ewd: {Up.weighed(rs, Up.Weigh{url, r0}) == wd : Up.Wd}
  {again_t(Up.tool.kept(wd, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag), g, rs, only)
    == still_t(Up.tool.kept(wd, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag),
      psays(again_t(Up.tool.kept(wd, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag), g, rs,
        only))) : Up.Pinned}

def t.kept(wd, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, hr0, ea, et, es, ewd):
  match wd:
    case Up.Wd{+nw}:
      t.knar(String.is_empty(nr0), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, nw, am, tip, tag, br, ec, hr0, ea,
        et, es, ewd, {==})
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

# LAW: a tip that is another commit, once ancestry is in
law t.onward:
  for asc: Up.Asc
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  {again_t(Up.tool.onward(asc, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs, only)
    == still_t(Up.tool.onward(asc, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br),
      psays(again_t(Up.tool.onward(asc, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs,
        only))) : Up.Pinned}

def t.onward(asc, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, ea, et):
  match asc:
    case Up.Asc{yes}:
      match yes:
        case True{}:
          t.weighed(Up.weighed(rs, Up.Weigh{url, tip}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, "",
            [Up.say.move(n, r0, tip, br)], am, tip,
            tag, br, ec, ea, et, {==})
        case False{}:
          {==}
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

# LAW: the tip against the pin
law t.same:
  for s: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for +tip: String
  for +tag: String
  for +br: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == Up.At{tip, tag, br} : Up.Tip}
  for es: {String.eq(r0, tip) == s : Bool}
  {again_t(Up.tool.same(s, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs, only)
    == still_t(Up.tool.same(s, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br),
      psays(again_t(Up.tool.same(s, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, tip, tag, br), g, rs,
        only))) : Up.Pinned}

def t.same(s, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, hr0, ea, et, es):
  match s:
    case True{}:
      t.kept(Up.weighed(rs, Up.Weigh{url, r0}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec,
        hr0, ea, et, es, {==})
    case False{}:
      t.onward(Up.onward(rs, Up.Above{url, r0, tip}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag,
        br, ec, ea, et)

# LAW: whatever tip the remote named
law t.tip:
  for t: Up.Tip
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for am: U.Aim
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  for et: {up.tip(am, rs, url) == t : Up.Tip}
  {again_t(Up.tool.tip(t, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only)
    == still_t(Up.tool.tip(t, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}),
      psays(again_t(Up.tool.tip(t, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only))) : Up.Pinned}

def t.tip(t, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, ec, hr0, ea, et):
  match t:
    case Up.At{+tip, +tag, +br}:
      t.same(String.eq(r0, tip), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, am, tip, tag, br, ec, hr0, ea, et,
        {==})
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: a pin with a commit, whatever it is asked
law t.aim:
  for am: U.Aim
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, n) == True{} : Bool}
  for hr0: {String.is_empty(r0) == False{} : Bool}
  for ea: {U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}) == am : U.Aim}
  {again_t(Up.tool.aim(am, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only)
    == still_t(Up.tool.aim(am, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}),
      psays(again_t(Up.tool.aim(am, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only))) : Up.Pinned}

def t.aim(am, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, hr0, ea):
  match am:
    case U.Hold{}:
      nec = Equal.sym(Bool, U.chosen(only, n), True{}, ec)
      %nec : {Up.tool.sel(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}})
        == pkept(M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, psays(Up.tool.sel(_, re(g, rs), M.Cli{n, e, b,
          M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Pinned}
      sa = Equal.sym(Up.Pinned,
        Up.tool.short(Bool.or(String.is_empty(r0), String.is_empty(nr0)), re(g, rs), M.Cli{n, e, b, M.Git{url, r0,
          tg, rt0, nr0, vd}}),
        Up.tool.aim(U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), re(g, rs), M.Cli{n, e, b, M.Git{url, r0, tg,
          rt0, nr0, vd}}),
        short_aim(Bool.or(String.is_empty(r0), String.is_empty(nr0)), re(g, rs), n, e, b, url, r0, tg,
          rt0, nr0, vd, hr0))
      %sa : {_ == pkept(M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, psays(_)) : Up.Pinned}
      nea = Equal.sym(U.Aim, U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), U.Hold{}, ea)
      %nea : {Up.tool.aim(_, re(g, rs), M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}})
        == pkept(M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, psays(Up.tool.aim(_, re(g, rs), M.Cli{n, e, b,
          M.Git{url, r0, tg, rt0, nr0, vd}}))) : Up.Pinned}
      {==}
    case U.Follow{+ref}:
      t.tip(Up.follow(rs, url, ref), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, U.Follow{ref}, ec, hr0, ea, {==})
    case U.Forward{}:
      t.tip(Up.forward(rs, url), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, U.Forward{}, ec, hr0, ea, {==})

# whether the ref a pin is pinned from names something
def named.ok(nm: Up.Named) -> Bool:
  match nm:
    case Up.Named{ref}:
      Bool.not(String.is_empty(ref))
    case Up.NamedWait{_a}:
      True{}
    case Up.NamedNo{_w}:
      True{}

# LAW: a branch a remote's HEAD names is a ref, when it names one
law br_ok:
  for name: String
  for +url: String
  {named.ok(Up.heads.branch(name, url)) == True{} : Bool}

def br_ok(name, _url):
  match name:
    case SNil{}:
      {==}
    case SCon{_h, _t}:
      {==}

law heads_ok:
  for said: Up.Said
  for +url: String
  {named.ok(Up.heads.said(said, url)) == True{} : Bool}

def heads_ok(said, url):
  match said:
    case Up.Said{text}:
      br_ok(Git.tip.branch(Git.rows(String.lines(text))), url)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

law best_ok:
  for best: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  {named.ok(Up.tags.best(String.is_empty(best), best, rs, url)) == True{} : Bool}

def best_ok(best, rs, url):
  match best:
    case SNil{}:
      heads_ok(Up.printed(rs, Up.Head{url}, "ls-remote " ++ url), url)
    case SCon{_h, _t}:
      {==}

law tags_ok:
  for said: Up.Said
  for +rs: List<&2, Up.Reply>
  for +url: String
  {named.ok(Up.tags.said(said, rs, url)) == True{} : Bool}

def tags_ok(said, rs, url):
  match said:
    case Up.Said{text}:
      best_ok(Git.choose(Git.tag.names(Git.rows(String.lines(text)))), rs, url)
    case Up.Unsaid{_why}:
      {==}
    case Up.Unasked{_ask}:
      {==}

# LAW: a pin with no commit is pinned from a ref that names something: its
# tag, or the greatest release tag, or the default branch
law ref_ok:
  for tg: String
  for +rs: List<&2, Up.Reply>
  for +url: String
  {named.ok(Up.tool.ref(String.is_empty(tg), rs, url, tg)) == True{} : Bool}

def ref_ok(tg, rs, url):
  match tg:
    case SNil{}:
      tags_ok(Up.printed(rs, Up.Tags{url}, "ls-remote " ++ url), rs, url)
    case SCon{_h, _t}:
      {==}

# LAW: the pin, with a nonempty ref written in as its tag, is asked about
# that ref
law ea_ref:
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +ref: String
  for +ne: {String.is_empty(ref) == False{} : Bool}
  {U.aim(True{}, M.Git{url, r0, Bool.pick(String, String.is_empty(ref), tg, ref), rt0, nr0, vd})
    == U.Follow{ref} : U.Aim}

def ea_ref(_url, _r0, tg, _rt0, _nr0, _vd, ref, ne):
  nes = Equal.sym(Bool, String.is_empty(ref), False{}, ne)
  %nes : {U.aim.tag(String.is_empty(Bool.pick(String, _, tg, ref)), Bool.pick(String, _, tg, ref))
    == U.Follow{ref} : U.Aim}
  nes2 = Equal.sym(Bool, String.is_empty(ref), False{}, ne)
  %nes2 : {U.aim.tag(_, ref) == U.Follow{ref} : U.Aim}
  {==}

# LAW: a pin with no commit, once its ref resolved
law t.resolved:
  for tp: Up.Tip
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for +ref: String
  for ec: {U.chosen(only, n) == True{} : Bool}
  for +ne: {String.is_empty(ref) == False{} : Bool}
  for et: {Up.follow(rs, url, ref) == tp : Up.Tip}
  {again_t(Up.tool.resolved(tp, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, ref), g, rs, only)
    == still_t(Up.tool.resolved(tp, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, ref),
      psays(again_t(Up.tool.resolved(tp, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, ref), g, rs,
        only))) : Up.Pinned}

def t.resolved(tp, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ref, ec, ne, et):
  match tp:
    case Up.At{+tip, +tag, +br}:
      t.weighed(Up.weighed(rs, Up.Weigh{url, tip}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ref, [],
        U.Follow{ref}, tip, tag, br, ec,
        ea_ref(url, r0, tg, rt0, nr0, vd, ref, ne), et, {==})
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

# LAW: a pin with no commit, once its ref is known
law t.named:
  for nm: Up.Named
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, n) == True{} : Bool}
  for eok: {named.ok(nm) == True{} : Bool}
  {again_t(Up.tool.named(nm, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, url), g, rs, only)
    == still_t(Up.tool.named(nm, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, url),
      psays(again_t(Up.tool.named(nm, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}, url), g, rs,
        only))) : Up.Pinned}

def t.named(nm, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, eok):
  match nm:
    case Up.Named{+ref}:
      t.resolved(Up.follow(rs, url, ref), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ref, ec,
        Eq.not.true(String.is_empty(ref), eok), {==})
    case Up.NamedWait{_ask}:
      {==}
    case Up.NamedNo{_why}:
      {==}

# LAW: a short pin, filled
law t.fill:
  for nf: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, n) == True{} : Bool}
  for enf: {String.is_empty(r0) == nf : Bool}
  {again_t(Up.tool.fill(nf, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only)
    == still_t(Up.tool.fill(nf, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}),
      psays(again_t(Up.tool.fill(nf, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only))) : Up.Pinned}

def t.fill(nf, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, enf):
  match nf:
    case True{}:
      t.named(Up.tool.ref(String.is_empty(tg), rs, url, tg), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec,
        ref_ok(tg, rs, url))
    case False{}:
      t.aim(U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, enf,
        {==})

# LAW: a selected pin from a repository, short or full
law t.short:
  for sh: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for +url: String
  for +r0: String
  for +tg: String
  for +rt0: String
  for +nr0: String
  for +vd: Bool
  for ec: {U.chosen(only, n) == True{} : Bool}
  for esh: {Bool.or(String.is_empty(r0), String.is_empty(nr0)) == sh : Bool}
  {again_t(Up.tool.short(sh, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs, only)
    == still_t(Up.tool.short(sh, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}),
      psays(again_t(Up.tool.short(sh, rs, M.Cli{n, e, b, M.Git{url, r0, tg, rt0, nr0, vd}}), g, rs,
        only))) : Up.Pinned}

def t.short(sh, g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, esh):
  match sh:
    case True{}:
      t.fill(String.is_empty(r0), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec, {==})
    case False{}:
      t.aim(U.aim(True{}, M.Git{url, r0, tg, rt0, nr0, vd}), g, rs, only, n, e, b, url, r0, tg, rt0, nr0, vd, ec,
        or_false_l(String.is_empty(r0), String.is_empty(nr0), esh), {==})

# LAW: whatever the upgrade makes of a tool pin, the next upgrade, against the
# same remote, keeps the pin it left, or stops as it did
law t.sel:
  for sel: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +n: String
  for +e: String
  for +b: String
  for s: M.Source
  for ec: {U.chosen(only, n) == sel : Bool}
  {again_t(Up.tool.sel(sel, rs, M.Cli{n, e, b, s}), g, rs, only)
    == still_t(Up.tool.sel(sel, rs, M.Cli{n, e, b, s}),
      psays(again_t(Up.tool.sel(sel, rs, M.Cli{n, e, b, s}), g, rs, only))) : Up.Pinned}

def t.sel(sel, g, rs, only, n, e, b, s, ec):
  match sel:
    case False{}:
      nec = Equal.sym(Bool, U.chosen(only, n), False{}, ec)
      %nec : {Up.tool.sel(_, re(g, rs), M.Cli{n, e, b, s})
        == pkept(M.Cli{n, e, b, s}, psays(Up.tool.sel(_, re(g, rs), M.Cli{n, e, b, s}))) : Up.Pinned}
      {==}
    case True{}:
      match s:
        case M.Hub{hv}:
          {==}
        case M.Git{+url, +r0, +tg, +rt0, +nr0, +vd}:
          t.short(Bool.or(String.is_empty(r0), String.is_empty(nr0)), g, rs, only, n, e, b, url, r0, tg,
            rt0, nr0, vd, ec, {==})
        case M.Member{mp, mn}:
          {==}

law t.one:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +t: M.Cli
  {again_t(Up.tool.sel(U.chosen(only, M.tool.name(t)), rs, t), g, rs, only)
    == still_t(Up.tool.sel(U.chosen(only, M.tool.name(t)), rs, t),
      psays(again_t(Up.tool.sel(U.chosen(only, M.tool.name(t)), rs, t), g, rs, only))) : Up.Pinned}

def t.one(g, rs, only, t):
  match t:
    case M.Cli{+n, +e, +b, s}:
      t.sel(U.chosen(only, n), g, rs, only, n, e, b, s, {==})

# whether a tool's fate that waits waits on a question
def pwok(p: Up.Pinned) -> Bool:
  match p:
    case Up.Pinned{_t, _m, _s}:
      True{}
    case Up.PinWait{a}:
      Bool.not(List.is_empty(&2, Up.Ask, a))
    case Up.PinHalt{_w}:
      True{}

law tpin_pwok:
  for short: Bool
  for +tool: M.Cli
  for +rev: String
  for +tag: String
  for +nar: String
  for says: List<&2, String>
  {pwok(Up.tool.pin(short, tool, rev, tag, nar, says)) == True{} : Bool}

def tpin_pwok(short, _tool, _rev, _tag, _nar, _says):
  match short:
    case True{}:
      {==}
    case False{}:
      {==}

law weighed_pwok:
  for wd: Up.Wd
  for +tool: M.Cli
  for +rev: String
  for +tag: String
  for says: List<&2, String>
  {pwok(Up.tool.weighed(wd, tool, rev, tag, says)) == True{} : Bool}

def weighed_pwok(wd, tool, rev, tag, says):
  match wd:
    case Up.Wd{+nar}:
      tpin_pwok(Bool.or(String.is_empty(rev), String.is_empty(nar)), tool, rev, tag, nar, says)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law resolved_pwok:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +ref: String
  {pwok(Up.tool.resolved(tip, rs, tool, ref)) == True{} : Bool}

def resolved_pwok(tip, rs, tool, ref):
  match tip:
    case Up.At{+rev, _tag, _branch}:
      weighed_pwok(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, ref, [])
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law named_pwok:
  for named: Up.Named
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +url: String
  {pwok(Up.tool.named(named, rs, tool, url)) == True{} : Bool}

def named_pwok(named, rs, tool, url):
  match named:
    case Up.Named{+ref}:
      resolved_pwok(Up.follow(rs, url, ref), rs, tool, ref)
    case Up.NamedWait{_ask}:
      {==}
    case Up.NamedNo{_why}:
      {==}

law tverdict_pwok:
  for verdict: U.Verdict
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +branch: String
  {pwok(Up.tool.verdict(verdict, rs, tool, tip, branch)) == True{} : Bool}

def tverdict_pwok(verdict, rs, tool, _tip, branch):
  match verdict:
    case U.Keep{}:
      {==}
    case U.Drift{}:
      {==}
    case U.Off{}:
      {==}
    case U.Advance{+rev, _tag}:
      weighed_pwok(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)), rev}), tool, rev, "",
        [Up.say.move(M.tool.name(tool), M.source.rev(M.tool.source(tool)), rev, branch)])

law tkept_nar_pwok:
  for fill: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  for +nar: String
  {pwok(Up.tool.kept.nar(fill, rs, tool, tip, tag, nar)) == True{} : Bool}

def tkept_nar_pwok(fill, rs, tool, tip, tag, nar):
  match fill:
    case True{}:
      tpin_pwok(Bool.or(String.is_empty(tip), String.is_empty(nar)), tool, tip, "", nar, [])
    case False{}:
      tverdict_pwok(U.judge(True{}, True{}, String.eq(M.source.nar(M.tool.source(tool)), nar), tip, tag),
        rs, tool, tip, "")

law tkept_pwok:
  for wd: Up.Wd
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  {pwok(Up.tool.kept(wd, rs, tool, tip, tag)) == True{} : Bool}

def tkept_pwok(wd, rs, tool, tip, tag):
  match wd:
    case Up.Wd{+nar}:
      tkept_nar_pwok(String.is_empty(M.source.nar(M.tool.source(tool))), rs, tool, tip, tag, nar)
    case Up.WdWait{_ask}:
      {==}
    case Up.WdNo{_why}:
      {==}

law tonward_pwok:
  for asc: Up.Asc
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  for +branch: String
  {pwok(Up.tool.onward(asc, rs, tool, tip, tag, branch)) == True{} : Bool}

def tonward_pwok(asc, rs, tool, tip, tag, branch):
  match asc:
    case Up.Asc{yes}:
      tverdict_pwok(U.judge(False{}, yes, False{}, tip, tag), rs, tool, tip, branch)
    case Up.AscWait{_ask}:
      {==}
    case Up.AscNo{_why}:
      {==}

law tsame_pwok:
  for same: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  for +tip: String
  for +tag: String
  for +branch: String
  {pwok(Up.tool.same(same, rs, tool, tip, tag, branch)) == True{} : Bool}

def tsame_pwok(same, rs, tool, tip, tag, branch):
  match same:
    case True{}:
      tkept_pwok(Up.weighed(rs, Up.Weigh{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool))}), rs, tool, tip, tag)
    case False{}:
      tonward_pwok(Up.onward(rs, Up.Above{M.source.url(M.tool.source(tool)),
        M.source.rev(M.tool.source(tool)), tip}), rs, tool, tip, tag, branch)

law ttip_pwok:
  for tip: Up.Tip
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pwok(Up.tool.tip(tip, rs, tool)) == True{} : Bool}

def ttip_pwok(tip, rs, tool):
  match tip:
    case Up.At{+rev, tag, branch}:
      tsame_pwok(String.eq(M.source.rev(M.tool.source(tool)), rev), rs, tool, rev, tag, branch)
    case Up.TipWait{_ask}:
      {==}
    case Up.TipNo{_why}:
      {==}

law taim_pwok:
  for aim: U.Aim
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pwok(Up.tool.aim(aim, rs, tool)) == True{} : Bool}

def taim_pwok(aim, rs, tool):
  match aim:
    case U.Hold{}:
      {==}
    case U.Follow{ref}:
      ttip_pwok(Up.follow(rs, M.source.url(M.tool.source(tool)), ref), rs, tool)
    case U.Forward{}:
      ttip_pwok(Up.forward(rs, M.source.url(M.tool.source(tool))), rs, tool)

law fill_pwok:
  for no_rev: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pwok(Up.tool.fill(no_rev, rs, tool)) == True{} : Bool}

def fill_pwok(no_rev, rs, tool):
  match no_rev:
    case True{}:
      named_pwok(Up.tool.ref(String.is_empty(M.source.tag(M.tool.source(tool))), rs,
        M.source.url(M.tool.source(tool)), M.source.tag(M.tool.source(tool))), rs, tool,
        M.source.url(M.tool.source(tool)))
    case False{}:
      taim_pwok(U.aim(True{}, M.tool.source(tool)), rs, tool)

law short_pwok:
  for short: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pwok(Up.tool.short(short, rs, tool)) == True{} : Bool}

def short_pwok(short, rs, tool):
  match short:
    case True{}:
      fill_pwok(String.is_empty(M.source.rev(M.tool.source(tool))), rs, tool)
    case False{}:
      taim_pwok(U.aim(True{}, M.tool.source(tool)), rs, tool)

law git_pwok:
  for git: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pwok(Up.tool.git(git, rs, tool)) == True{} : Bool}

def git_pwok(git, rs, tool):
  match git:
    case False{}:
      {==}
    case True{}:
      short_pwok(Bool.or(String.is_empty(M.source.rev(M.tool.source(tool))),
        String.is_empty(M.source.nar(M.tool.source(tool)))), rs, tool)

# LAW: whatever the upgrade makes of one tool, what it leaves in the ledger has
# the tool's name
law sel_pwok:
  for sel: Bool
  for +rs: List<&2, Up.Reply>
  for +tool: M.Cli
  {pwok(Up.tool.sel(sel, rs, tool)) == True{} : Bool}

def sel_pwok(sel, rs, tool):
  match sel:
    case False{}:
      {==}
    case True{}:
      git_pwok(M.source.is_git(M.tool.source(tool)), rs, tool)

# ---------------------------------------------------------------------------
# the walks, upgraded again

# the dependencies a walk leaves
def dd.ds(dd: Up.Deps) -> List<&2, M.Dep>:
  Up.Deps{ds, _ss, _es, _m, _sy, _tr, _asks, _bad} = dd
  ds

# the lines a walk says
def dd.says(dd: Up.Deps) -> List<&2, String>:
  Up.Deps{_ds, _ss, _es, _m, sy, _tr, _asks, _bad} = dd
  sy

# a walk that keeps every dependency and asks nothing
def dsettle(ds: List<&2, M.Dep>, s: List<&2, String>) -> Up.Deps:
  Up.Deps{ds, [], [], False{}, s, [], [], ""}

# whether a walk refuses or still asks
def dunc(dd: Up.Deps) -> Bool:
  Up.Deps{_ds, _ss, _es, _m, _sy, _tr, asks, bad} = dd
  Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks)))

# the dependencies a walk leaves when it neither refuses, asks, nor moves a
# pin, else the ones it was given
def dstay(dd: Up.Deps, +ds: List<&2, M.Dep>) -> List<&2, M.Dep>:
  Up.Deps{dds, _ss, _es, dm, _sy, _tr, asks, bad} = dd
  Bool.pick(List<&2, M.Dep>,
    Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))), dm),
    ds, dds)

# LAW: one step of the walk: the next run keeps the pin this one left in front
law w.step:
  for f: Up.Fate
  for r: Up.Deps
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for ha: {again(f, g, rs, only, hub) == M1.still(f, fsays(again(f, g, rs, only, hub))) : Up.Fate}
  for ih: {Up.deps.walk(re(g, rs), only, hub, dd.ds(r))
    == dsettle(dd.ds(r), dd.says(Up.deps.walk(re(g, rs), only, hub, dd.ds(r)))) : Up.Deps}
  {Up.deps.walk(re(g, rs), only, hub, dd.ds(Up.deps.join(f, r)))
    == dsettle(dd.ds(Up.deps.join(f, r)), dd.says(Up.deps.walk(re(g, rs), only, hub,
      dd.ds(Up.deps.join(f, r))))) : Up.Deps}

def w.step(f, r, g, rs, only, hub, ha, ih):
  match f:
    case Up.Became{+d, o, n, p, m, s, t}:
      match r:
        case Up.Deps{+ds, ss, es, any, sy, tr, asks, bad}:
          nha = Equal.sym(Up.Fate, again.d(d, g, rs, only, hub),
            M1.kept(d, fsays(again.d(d, g, rs, only, hub))), ha)
          %nha : {Up.deps.join(_, Up.deps.walk(re(g, rs), only, hub, ds))
            == dsettle(d <> ds, dd.says(Up.deps.join(_, Up.deps.walk(re(g, rs), only, hub, ds))))
            : Up.Deps}
          nih = Equal.sym(Up.Deps, Up.deps.walk(re(g, rs), only, hub, ds),
            dsettle(ds, dd.says(Up.deps.walk(re(g, rs), only, hub, ds))), ih)
          %nih : {Up.deps.join(M1.kept(d, fsays(again.d(d, g, rs, only, hub))), _)
            == dsettle(d <> ds, dd.says(Up.deps.join(M1.kept(d, fsays(again.d(d, g, rs, only, hub))), _)))
            : Up.Deps}
          {==}
    case Up.Waits{+a}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          ih
    case Up.Halts{+w}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, tr, asks, bad}:
          ih

# LAW: the next upgrade, against the same remote, walks the dependencies this
# one left and keeps every one: it moves nothing, removes nothing, stops
# naming no hash, checks nothing out, asks nothing and refuses nothing
law w.all:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  {Up.deps.walk(re(g, rs), only, hub, dd.ds(Up.deps.walk(rs, only, hub, ds)))
    == dsettle(dd.ds(Up.deps.walk(rs, only, hub, ds)), dd.says(Up.deps.walk(re(g, rs), only, hub,
      dd.ds(Up.deps.walk(rs, only, hub, ds))))) : Up.Deps}

def w.all(g, rs, only, hub, ds):
  match ds:
    case []:
      {==}
    case +h <> +t:
      w.step(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        Up.deps.walk(rs, only, hub, t), g, rs, only, hub, a.one(g, rs, only, hub, h), w.all(g, rs, only, hub, t))

# LAW: an `or` with a left half that answered True answers the same whatever
# its right half is
law or_left_same:
  for u: Bool
  for +a: Bool
  for +b: Bool
  for e: {u == True{} : Bool}
  {Bool.or(u, a) == Bool.or(u, b) : Bool}

def or_left_same(u, a, b, e):
  ne = Equal.sym(Bool, u, True{}, e)
  %ne : {Bool.or(_, a) == Bool.or(_, b) : Bool}
  {==}

# LAW: a scan of names whose rest answers the same answers the same
law known.step_cong:
  for c: Bool
  for +u: Bool
  for +k1: Bool
  for +k2: Bool
  for ih: {Bool.or(u, k1) == Bool.or(u, k2) : Bool}
  {Bool.or(u, U.known.step(c, _x => k1)) == Bool.or(u, U.known.step(c, _y => k2)) : Bool}

def known.step_cong(c, _u, _k1, _k2, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: a walk that waits with a question refuses or asks
law waits_unc:
  for a: List<&2, Up.Ask>
  for +bad: String
  for +asks: List<&2, Up.Ask>
  for e: {Bool.not(List.is_empty(&2, Up.Ask, a)) == True{} : Bool}
  {Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks))))
    == True{} : Bool}

def waits_unc(a, bad, asks, e):
  match a:
    case []:
      Eq.bit.absurd(&2, {Bool.or(Bool.not(String.is_empty(bad)),
        Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, [], asks)))) == True{} : Bool}, e)
    case x <> xs:
      mv.or_r(Bool.not(String.is_empty(bad)), True{}, {==})

# LAW: one step of the walk keeps the names the ledger can be asked about,
# unless the walk refuses or asks
law kd.step:
  for f: Up.Fate
  for r: Up.Deps
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for +x: String
  for fine: {mv.fine(f, M.dep.name(h)) == (M.dep.name(h), True{}) : String & Bool}
  for ih: {Bool.or(dunc(r), U.known.in(dd.ds(r), x)) == Bool.or(dunc(r), U.known.in(t, x)) : Bool}
  {Bool.or(dunc(Up.deps.join(f, r)), U.known.in(dd.ds(Up.deps.join(f, r)), x))
    == Bool.or(dunc(Up.deps.join(f, r)), U.known.in(h <> t, x)) : Bool}

def kd.step(f, r, h, t, x, fine, ih):
  match f:
    case Up.Became{d, o, n, p, m, s, tr}:
      match r:
        case Up.Deps{+ds, ss, es, any, sy, trr, +asks, +bad}:
          en = Equal.cong(String & Bool, String, q => mv.fst(q), (M.dep.name(d), True{}),
            (M.dep.name(h), True{}), fine)
          nen = Equal.sym(String, M.dep.name(d), M.dep.name(h), en)
          %nen : {Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
              U.known.step(String.eq(_, x), _u => U.known.in(ds, x)))
            == Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
              U.known.step(String.eq(M.dep.name(h), x), _v => U.known.in(t, x))) : Bool}
          known.step_cong(String.eq(M.dep.name(h), x),
            Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
            U.known.in(ds, x), U.known.in(t, x), ih)
    case Up.Waits{+a}:
      match r:
        case Up.Deps{+ds, ss, es, +any, sy, trr, +asks, +bad}:
          or_left_same(Bool.or(Bool.not(String.is_empty(bad)),
              Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))),
            U.known.in(ds, x), U.known.in(h <> t, x),
            waits_unc(a, bad, asks, Equal.cong(String & Bool, Bool, q => mv.snd(q),
              (M.dep.name(h), Bool.not(List.is_empty(&2, Up.Ask, a))), (M.dep.name(h), True{}), fine)))
    case Up.Halts{+w}:
      match r:
        case Up.Deps{ds, ss, es, any, sy, trr, +asks, bad}:
          or_left_same(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
              Bool.not(List.is_empty(&2, Up.Ask, asks))),
            U.known.in(ds, x), U.known.in(h <> t, x),
            mv.or_l(Bool.not(String.is_empty(Up.halt.why(w))), Bool.not(List.is_empty(&2, Up.Ask, asks)),
              mv.halt_not(w)))

# LAW: a walk that neither refuses nor asks keeps every name the ledger can
# be asked about
law kd.all:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  for +x: String
  {Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known.in(dd.ds(Up.deps.walk(rs, only, hub, ds)), x))
    == Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known.in(ds, x)) : Bool}

def kd.all(rs, only, hub, ds, x):
  match ds:
    case []:
      {==}
    case +h <> +t:
      kd.step(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        Up.deps.walk(rs, only, hub, t), h, t, x,
        mv.fine_one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        kd.all(rs, only, hub, t, x))

# LAW: and so the dependency `--package` names, when there is one
law kd.known.go:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  {Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known.go(b, dd.ds(Up.deps.walk(rs, only, hub, ds)), only))
    == Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known.go(b, ds, only)) : Bool}

def kd.known.go(b, rs, only, hub, ds):
  match b:
    case True{}:
      {==}
    case False{}:
      kd.all(rs, only, hub, ds, only)

law kd.known:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  {Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known(only, dd.ds(Up.deps.walk(rs, only, hub, ds))))
    == Bool.or(dunc(Up.deps.walk(rs, only, hub, ds)), U.known(only, ds)) : Bool}

def kd.known(rs, only, hub, ds):
  kd.known.go(String.is_empty(only), rs, only, hub, ds)

# LAW: a list kept in front of a list kept
law pick_cons:
  for c: Bool
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for +d: M.Dep
  for +ds: List<&2, M.Dep>
  for hd: {d == h : M.Dep}
  for ih: {Bool.pick(List<&2, M.Dep>, c, t, ds) == t : List<&2, M.Dep>}
  {Bool.pick(List<&2, M.Dep>, c, h <> t, d <> ds) == h <> t : List<&2, M.Dep>}

def pick_cons(c, h, t, d, ds, hd, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      Equal.trans(List<&2, M.Dep>, d <> ds, h <> ds, h <> t,
        Equal.cong(M.Dep, List<&2, M.Dep>, y => y <> ds, d, h, hd),
        Equal.cong(List<&2, M.Dep>, List<&2, M.Dep>, y => h <> y, ds, t, ih))

# LAW: a pick whose condition answered True is its first
law pick_true:
  for c: Bool
  for +a: List<&2, M.Dep>
  for +b: List<&2, M.Dep>
  for e: {c == True{} : Bool}
  {Bool.pick(List<&2, M.Dep>, c, a, b) == a : List<&2, M.Dep>}

def pick_true(c, a, b, e):
  ne = Equal.sym(Bool, c, True{}, e)
  %ne : {Bool.pick(List<&2, M.Dep>, _, a, b) == a : List<&2, M.Dep>}
  {==}

# LAW: a pin in front, whether it moved or not
law dq.moved:
  for m: Bool
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for +d: M.Dep
  for +ds: List<&2, M.Dep>
  for +any: Bool
  for +asks: List<&2, Up.Ask>
  for +bad: String
  for hb: {Bool.pick(M.Dep, m, h, d) == h : M.Dep}
  for ih: {Bool.pick(List<&2, M.Dep>, Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
    Bool.not(List.is_empty(&2, Up.Ask, asks))), any), t, ds) == t : List<&2, M.Dep>}
  {Bool.pick(List<&2, M.Dep>, Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
    Bool.not(List.is_empty(&2, Up.Ask, asks))), Bool.or(m, any)), h <> t, d <> ds) == h <> t
    : List<&2, M.Dep>}

def dq.moved(m, h, t, d, ds, any, asks, bad, hb, ih):
  match m:
    case True{}:
      pick_true(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
          Bool.not(List.is_empty(&2, Up.Ask, asks))), True{}), h <> t, d <> ds,
        mv.or_r(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
          True{}, {==}))
    case False{}:
      pick_cons(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
          Bool.not(List.is_empty(&2, Up.Ask, asks))), any), h, t, d, ds, hb, ih)

# LAW: one step of the walk: a pin that says it did not move is the one it was
law dq.step:
  for f: Up.Fate
  for r: Up.Deps
  for +h: M.Dep
  for +t: List<&2, M.Dep>
  for hb: {M1.back(f, h) == h : M.Dep}
  for fine: {mv.fine(f, M.dep.name(h)) == (M.dep.name(h), True{}) : String & Bool}
  for ih: {dstay(r, t) == t : List<&2, M.Dep>}
  {dstay(Up.deps.join(f, r), h <> t) == h <> t : List<&2, M.Dep>}

def dq.step(f, r, h, t, hb, fine, ih):
  match f:
    case Up.Became{+d, o, n, p, m, s, tr}:
      match r:
        case Up.Deps{+ds, ss, es, +any, sy, trr, +asks, +bad}:
          dq.moved(m, h, t, d, ds, any, asks, bad, hb, ih)
    case Up.Waits{+a}:
      match r:
        case Up.Deps{+ds, ss, es, +any, sy, trr, +asks, +bad}:
          pick_true(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
              Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))), any), h <> t, ds,
            mv.or_l(Bool.or(Bool.not(String.is_empty(bad)),
                Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))), any,
              waits_unc(a, bad, asks, Equal.cong(String & Bool, Bool, q => mv.snd(q),
                (M.dep.name(h), Bool.not(List.is_empty(&2, Up.Ask, a))), (M.dep.name(h), True{}), fine))))
    case Up.Halts{+w}:
      match r:
        case Up.Deps{ds, ss, es, +any, sy, trr, +asks, bad}:
          pick_true(Bool.or(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
              Bool.not(List.is_empty(&2, Up.Ask, asks))), any), h <> t, ds,
            mv.or_l(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
                Bool.not(List.is_empty(&2, Up.Ask, asks))), any,
              mv.or_l(Bool.not(String.is_empty(Up.halt.why(w))), Bool.not(List.is_empty(&2, Up.Ask, asks)),
                mv.halt_not(w))))

# LAW: a walk that neither refuses, asks, nor moves a pin leaves the
# dependencies it was given
law dq.all:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +hub: String
  for +ds: List<&2, M.Dep>
  {dstay(Up.deps.walk(rs, only, hub, ds), ds) == ds : List<&2, M.Dep>}

def dq.all(rs, only, hub, ds):
  match ds:
    case []:
      {==}
    case +h <> +t:
      dq.step(Up.dep.one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        Up.deps.walk(rs, only, hub, t), h, t,
        one_back(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        mv.fine_one(U.aim(U.chosen(only, M.dep.name(h)), M.source.dep(h)), rs, only, hub, h),
        dq.all(rs, only, hub, t))

# the tool pins a walk leaves
def tt.ts(tt: Up.Tools) -> List<&2, M.Cli>:
  Up.Tools{ts, _m, _sy, _asks, _bad} = tt
  ts

# the lines a walk over tools says
def tt.says(tt: Up.Tools) -> List<&2, String>:
  Up.Tools{_ts, _m, sy, _asks, _bad} = tt
  sy

# a walk that keeps every tool pin and asks nothing
def tsettle(ts: List<&2, M.Cli>, s: List<&2, String>) -> Up.Tools:
  Up.Tools{ts, False{}, s, [], ""}

# whether a walk over tools refuses or still asks
def tunc(tt: Up.Tools) -> Bool:
  Up.Tools{_ts, _m, _sy, asks, bad} = tt
  Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks)))

# the tool pins a walk leaves when it neither refuses, asks, nor moves a pin,
# else the ones it was given
def tstay(tt: Up.Tools, +ts: List<&2, M.Cli>) -> List<&2, M.Cli>:
  Up.Tools{tts, tm, _sy, asks, bad} = tt
  Bool.pick(List<&2, M.Cli>,
    Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))), tm),
    ts, tts)

# LAW: one step of the walk over tools
law tw.step:
  for p: Up.Pinned
  for r: Up.Tools
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for ha: {again_t(p, g, rs, only) == still_t(p, psays(again_t(p, g, rs, only))) : Up.Pinned}
  for ih: {Up.tools.walk(re(g, rs), only, tt.ts(r))
    == tsettle(tt.ts(r), tt.says(Up.tools.walk(re(g, rs), only, tt.ts(r)))) : Up.Tools}
  {Up.tools.walk(re(g, rs), only, tt.ts(Up.tools.join(p, r)))
    == tsettle(tt.ts(Up.tools.join(p, r)), tt.says(Up.tools.walk(re(g, rs), only,
      tt.ts(Up.tools.join(p, r))))) : Up.Tools}

def tw.step(p, r, g, rs, only, ha, ih):
  match p:
    case Up.Pinned{+t, m, s}:
      match r:
        case Up.Tools{+ts, any, sy, asks, bad}:
          nha = Equal.sym(Up.Pinned, again_t.t(t, g, rs, only),
            pkept(t, psays(again_t.t(t, g, rs, only))), ha)
          %nha : {Up.tools.join(_, Up.tools.walk(re(g, rs), only, ts))
            == tsettle(t <> ts, tt.says(Up.tools.join(_, Up.tools.walk(re(g, rs), only, ts))))
            : Up.Tools}
          nih = Equal.sym(Up.Tools, Up.tools.walk(re(g, rs), only, ts),
            tsettle(ts, tt.says(Up.tools.walk(re(g, rs), only, ts))), ih)
          %nih : {Up.tools.join(pkept(t, psays(again_t.t(t, g, rs, only))), _)
            == tsettle(t <> ts, tt.says(Up.tools.join(pkept(t, psays(again_t.t(t, g, rs, only))), _)))
            : Up.Tools}
          {==}
    case Up.PinWait{+a}:
      match r:
        case Up.Tools{+ts, any, sy, asks, bad}:
          ih
    case Up.PinHalt{+w}:
      match r:
        case Up.Tools{+ts, any, sy, asks, bad}:
          ih

# LAW: the next upgrade, against the same remote, keeps every tool pin this
# one left
law tw.all:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Cli>
  {Up.tools.walk(re(g, rs), only, tt.ts(Up.tools.walk(rs, only, ts)))
    == tsettle(tt.ts(Up.tools.walk(rs, only, ts)), tt.says(Up.tools.walk(re(g, rs), only,
      tt.ts(Up.tools.walk(rs, only, ts))))) : Up.Tools}

def tw.all(g, rs, only, ts):
  match ts:
    case []:
      {==}
    case +h <> +t:
      tw.step(Up.tool.sel(U.chosen(only, M.tool.name(h)), rs, h), Up.tools.walk(rs, only, t), g, rs, only,
        t.one(g, rs, only, h), tw.all(g, rs, only, t))

# LAW: a scan of tool names whose rest answers the same answers the same
law tool.step_cong:
  for c: Bool
  for +u: Bool
  for +k1: Bool
  for +k2: Bool
  for ih: {Bool.or(u, k1) == Bool.or(u, k2) : Bool}
  {Bool.or(u, M.tool.step(c, _x => k1)) == Bool.or(u, M.tool.step(c, _y => k2)) : Bool}

def tool.step_cong(c, _u, _k1, _k2, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: one step of the walk over tools keeps the names `--package` can ask
# about, unless the walk refuses or asks
law tkd.step:
  for p: Up.Pinned
  for r: Up.Tools
  for +h: M.Cli
  for +t: List<&2, M.Cli>
  for +x: String
  for nm: {pinned.name(p, M.tool.name(h)) == M.tool.name(h) : String}
  for ok: {pwok(p) == True{} : Bool}
  for ih: {Bool.or(tunc(r), M.tool.has(tt.ts(r), x)) == Bool.or(tunc(r), M.tool.has(t, x)) : Bool}
  {Bool.or(tunc(Up.tools.join(p, r)), M.tool.has(tt.ts(Up.tools.join(p, r)), x))
    == Bool.or(tunc(Up.tools.join(p, r)), M.tool.has(h <> t, x)) : Bool}

def tkd.step(p, r, h, t, x, nm, ok, ih):
  match p:
    case Up.Pinned{pt, m, s}:
      match r:
        case Up.Tools{+ts, any, sy, +asks, +bad}:
          nen = Equal.sym(String, M.tool.name(pt), M.tool.name(h), nm)
          %nen : {Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
              M.tool.step(String.eq(_, x), _u => M.tool.has(ts, x)))
            == Bool.or(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
              M.tool.step(String.eq(M.tool.name(h), x), _v => M.tool.has(t, x))) : Bool}
          tool.step_cong(String.eq(M.tool.name(h), x),
            Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
            M.tool.has(ts, x), M.tool.has(t, x), ih)
    case Up.PinWait{+a}:
      match r:
        case Up.Tools{+ts, any, sy, +asks, +bad}:
          or_left_same(Bool.or(Bool.not(String.is_empty(bad)),
              Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))),
            M.tool.has(ts, x), M.tool.has(h <> t, x), waits_unc(a, bad, asks, ok))
    case Up.PinHalt{+w}:
      match r:
        case Up.Tools{+ts, any, sy, +asks, bad}:
          or_left_same(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
              Bool.not(List.is_empty(&2, Up.Ask, asks))),
            M.tool.has(ts, x), M.tool.has(h <> t, x),
            mv.or_l(Bool.not(String.is_empty(Up.halt.why(w))), Bool.not(List.is_empty(&2, Up.Ask, asks)),
              mv.halt_not(w)))

law tkd.all:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Cli>
  for +x: String
  {Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.has(tt.ts(Up.tools.walk(rs, only, ts)), x))
    == Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.has(ts, x)) : Bool}

def tkd.all(rs, only, ts, x):
  match ts:
    case []:
      {==}
    case +h <> +t:
      tkd.step(Up.tool.sel(U.chosen(only, M.tool.name(h)), rs, h), Up.tools.walk(rs, only, t), h, t, x,
        sel_name(U.chosen(only, M.tool.name(h)), rs, h), sel_pwok(U.chosen(only, M.tool.name(h)), rs, h),
        tkd.all(rs, only, t, x))

law tkd.known.go:
  for b: Bool
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Cli>
  {Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.known.go(b, tt.ts(Up.tools.walk(rs, only, ts)), only))
    == Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.known.go(b, ts, only)) : Bool}

def tkd.known.go(b, rs, only, ts):
  match b:
    case True{}:
      {==}
    case False{}:
      tkd.all(rs, only, ts, only)

law tkd.known:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Cli>
  {Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.known(only, tt.ts(Up.tools.walk(rs, only, ts))))
    == Bool.or(tunc(Up.tools.walk(rs, only, ts)), M.tool.known(only, ts)) : Bool}

def tkd.known(rs, only, ts):
  tkd.known.go(String.is_empty(only), rs, only, ts)

# LAW: a list of tool pins kept in front of a list kept
law tpick_cons:
  for c: Bool
  for +h: M.Cli
  for +t: List<&2, M.Cli>
  for +d: M.Cli
  for +ds: List<&2, M.Cli>
  for hd: {d == h : M.Cli}
  for ih: {Bool.pick(List<&2, M.Cli>, c, t, ds) == t : List<&2, M.Cli>}
  {Bool.pick(List<&2, M.Cli>, c, h <> t, d <> ds) == h <> t : List<&2, M.Cli>}

def tpick_cons(c, h, t, d, ds, hd, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      Equal.trans(List<&2, M.Cli>, d <> ds, h <> ds, h <> t,
        Equal.cong(M.Cli, List<&2, M.Cli>, y => y <> ds, d, h, hd),
        Equal.cong(List<&2, M.Cli>, List<&2, M.Cli>, y => h <> y, ds, t, ih))

law tpick_true:
  for c: Bool
  for +a: List<&2, M.Cli>
  for +b: List<&2, M.Cli>
  for e: {c == True{} : Bool}
  {Bool.pick(List<&2, M.Cli>, c, a, b) == a : List<&2, M.Cli>}

def tpick_true(c, a, b, e):
  ne = Equal.sym(Bool, c, True{}, e)
  %ne : {Bool.pick(List<&2, M.Cli>, _, a, b) == a : List<&2, M.Cli>}
  {==}

law tq.moved:
  for m: Bool
  for +h: M.Cli
  for +t: List<&2, M.Cli>
  for +d: M.Cli
  for +ds: List<&2, M.Cli>
  for +any: Bool
  for +asks: List<&2, Up.Ask>
  for +bad: String
  for hb: {Bool.pick(M.Cli, m, h, d) == h : M.Cli}
  for ih: {Bool.pick(List<&2, M.Cli>, Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
    Bool.not(List.is_empty(&2, Up.Ask, asks))), any), t, ds) == t : List<&2, M.Cli>}
  {Bool.pick(List<&2, M.Cli>, Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
    Bool.not(List.is_empty(&2, Up.Ask, asks))), Bool.or(m, any)), h <> t, d <> ds) == h <> t
    : List<&2, M.Cli>}

def tq.moved(m, h, t, d, ds, any, asks, bad, hb, ih):
  match m:
    case True{}:
      tpick_true(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
          Bool.not(List.is_empty(&2, Up.Ask, asks))), True{}), h <> t, d <> ds,
        mv.or_r(Bool.or(Bool.not(String.is_empty(bad)), Bool.not(List.is_empty(&2, Up.Ask, asks))),
          True{}, {==}))
    case False{}:
      tpick_cons(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
          Bool.not(List.is_empty(&2, Up.Ask, asks))), any), h, t, d, ds, hb, ih)

law tq.step:
  for p: Up.Pinned
  for r: Up.Tools
  for +h: M.Cli
  for +t: List<&2, M.Cli>
  for hb: {tback(p, h) == h : M.Cli}
  for ok: {pwok(p) == True{} : Bool}
  for ih: {tstay(r, t) == t : List<&2, M.Cli>}
  {tstay(Up.tools.join(p, r), h <> t) == h <> t : List<&2, M.Cli>}

def tq.step(p, r, h, t, hb, ok, ih):
  match p:
    case Up.Pinned{+d, m, s}:
      match r:
        case Up.Tools{+ds, +any, sy, +asks, +bad}:
          tq.moved(m, h, t, d, ds, any, asks, bad, hb, ih)
    case Up.PinWait{+a}:
      match r:
        case Up.Tools{+ds, +any, sy, +asks, +bad}:
          tpick_true(Bool.or(Bool.or(Bool.not(String.is_empty(bad)),
              Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))), any), h <> t, ds,
            mv.or_l(Bool.or(Bool.not(String.is_empty(bad)),
                Bool.not(List.is_empty(&2, Up.Ask, List.append(&2, Up.Ask, a, asks)))), any,
              waits_unc(a, bad, asks, ok)))
    case Up.PinHalt{+w}:
      match r:
        case Up.Tools{+ds, +any, sy, +asks, bad}:
          tpick_true(Bool.or(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
              Bool.not(List.is_empty(&2, Up.Ask, asks))), any), h <> t, ds,
            mv.or_l(Bool.or(Bool.not(String.is_empty(Up.halt.why(w))),
                Bool.not(List.is_empty(&2, Up.Ask, asks))), any,
              mv.or_l(Bool.not(String.is_empty(Up.halt.why(w))), Bool.not(List.is_empty(&2, Up.Ask, asks)),
                mv.halt_not(w))))

law tq.all:
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ts: List<&2, M.Cli>
  {tstay(Up.tools.walk(rs, only, ts), ts) == ts : List<&2, M.Cli>}

def tq.all(rs, only, ts):
  match ts:
    case []:
      {==}
    case +h <> +t:
      tq.step(Up.tool.sel(U.chosen(only, M.tool.name(h)), rs, h), Up.tools.walk(rs, only, t), h, t,
        sel_tback(U.chosen(only, M.tool.name(h)), rs, h), sel_pwok(U.chosen(only, M.tool.name(h)), rs, h),
        tq.all(rs, only, t))

# ---------------------------------------------------------------------------
# the upgrade, upgraded again

# what an upgrade decided, less the lines it says
def view(nx: Up.Next) -> Up.Next:
  Up.Next{mo, rd, st, ak, tr, vs, _sy, ed, fd, dr, sw} = nx
  Up.Next{mo, rd, st, ak, tr, vs, [], ed, fd, dr, sw}

# the second upgrade's decision, and the ledger the first one's lock was made
# from
def core.lhs(+nx: Up.Next, +only: String, +g: String, +rs: List<&2, Up.Reply>) -> Up.Next & M.Read:
  (view(Up.next(only, Up.next.model(nx), re(g, rs))), Up.next.read(nx))

# what they are: the target, and the ledger the first one wrote, read
def core.rhs(+nx: Up.Next, +g: String, ledger: Maybe<&2, String>) -> Up.Next & M.Read:
  (M1.target(Up.next.model(nx), g), W.parsed(D2.ledger.left(Up.next.edits(nx), ledger)))

# LAW: a pair of equals
law pair_eq:
  for a1: Up.Next
  for a2: Up.Next
  for b1: M.Read
  for b2: M.Read
  for e1: {a1 == a2 : Up.Next}
  for e2: {b1 == b2 : M.Read}
  {(a1, b1) == (a2, b2) : Up.Next & M.Read}

def pair_eq(a1, a2, b1, b2, e1, e2):
  Equal.trans(Up.Next & M.Read, (a1, b1), (a2, b1), (a2, b2),
    Equal.cong(Up.Next, Up.Next & M.Read, x => (x, b1), a1, a2, e1),
    Equal.cong(M.Read, Up.Next & M.Read, y => (a2, y), b1, b2, e2))

# LAW: an upgrade that writes at most `.gitignore` leaves ez.toml as it was
law li:
  for b: Bool
  for +allow: String
  for +ledger: Maybe<&2, String>
  {D2.ledger.left(Up.edit.if(b, ".gitignore", allow, []), ledger) == ledger : Maybe<&2, String>}

def li(b, _allow, _ledger):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: an upgrade of a ledger whose every pin is at its tip, against the same
# remote, decides the target: the ledger as it is, and nothing moved
law c.second:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Cli>
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for kn: {Bool.or(U.known(only, dds), M.tool.known(only, tts)) == True{} : Bool}
  {view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}}, re(g,
    rs))) == M1.target(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}}, g) : Up.Next}

def c.second(g, rs, only, name, entry, bin, hub, hubpa, hubpv, dds, tts, hw, tw, kn):
  nkn = Equal.sym(Bool, Bool.or(U.known(only, dds), M.tool.known(only, tts)), True{}, kn)
  %nkn : {view(Up.known(_, only, re(g, rs), M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds,
    tts})) == M1.target(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}}, g) : Up.Next}
  nhw = Equal.sym(Up.Deps, Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds), dsettle(dds, dd.says(Up.deps.walk(re(g,
    rs), only, M.hub.or(hub), dds))), hw)
  %nhw : {view(Up.pins(_, Up.tools.walk(re(g, rs), only, tts), re(g, rs), M.Manifest{name, entry, bin, hub, hubpa,
    hubpv, dds,
    tts})) == M1.target(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}}, g) : Up.Next}
  ntw = Equal.sym(Up.Tools, Up.tools.walk(re(g, rs), only, tts), tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only,
    tts))), tw)
  %ntw : {view(Up.pins(dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds))), _, re(g, rs),
    M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}))
    == M1.target(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}}, g) : Up.Next}
  {==}

# LAW: and one that moved nothing is one whose pins are the ones it walked
law c.same:
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Cli>
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for kn: {Bool.or(U.known(only, dds), M.tool.known(only, tts)) == True{} : Bool}
  for hq: {dds == ds : List<&2, M.Dep>}
  for tq: {tts == ts : List<&2, M.Cli>}
  {view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}}, re(g,
    rs))) == M1.target(M.Good{M.Manifest{name,
    entry, bin, hub, hubpa, hubpv, ds, ts}}, g) : Up.Next}

def c.same(g, rs, only, name, entry, bin, hub, hubpa, hubpv, _ds, ts, dds, tts, hw, tw, kn, hq, tq):
  %hq : {view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, _, ts}}, re(g, rs)))
    == M1.target(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, _, ts}}, g) : Up.Next}
  %tq : {view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, _}}, re(g, rs)))
    == M1.target(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, _}}, g) : Up.Next}
  c.second(g, rs, only, name, entry, bin, hub, hubpa, hubpv, dds, tts, hw, tw, kn)

# LAW: the known names, walked
law c.kn:
  for +only: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +tts: List<&2, M.Cli>
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hk: {U.known(only, dds) == U.known(only, ds) : Bool}
  for tk: {M.tool.known(only, tts) == M.tool.known(only, ts) : Bool}
  {Bool.or(U.known(only, dds), M.tool.known(only, tts)) == True{} : Bool}

def c.kn(only, ds, ts, dds, tts, ek, hk, tk):
  Equal.trans(Bool, Bool.or(U.known(only, dds), M.tool.known(only, tts)),
    Bool.or(U.known(only, ds), M.tool.known(only, tts)), True{},
    Equal.cong(Bool, Bool, x => Bool.or(x, M.tool.known(only, tts)), U.known(only, dds), U.known(only, ds), hk),
    Equal.trans(Bool, Bool.or(U.known(only, ds), M.tool.known(only, tts)),
      Bool.or(U.known(only, ds), M.tool.known(only, ts)), True{},
      Equal.cong(Bool, Bool, y => Bool.or(U.known(only, ds), y), M.tool.known(only, tts),
        M.tool.known(only, ts), tk),
      ek))

# LAW: every answer in; whether a pin moved decides the ledger the first run
# wrote and the second reads
law c.done:
  for dm: Bool
  for tm: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Cli>
  for +tsy: List<&2, String>
  for +ig: String
  for +fs: List<&2, Up.Found>
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for hk: {U.known(only, dds) == U.known(only, ds) : Bool}
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for tk: {M.tool.known(only, tts) == M.tool.known(only, ts) : Bool}
  for tq: {Bool.pick(List<&2, M.Cli>, tm, ts, tts) == ts : List<&2, M.Cli>}
  {core.lhs(Up.done(M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""},
    Up.Tools{tts, tm, tsy, [], ""}, ig, fs), only, g, rs) == core.rhs(Up.done(M.Manifest{name, entry, bin, hub, hubpa,
      hubpv, ds,
      ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig, fs), g,
        ledger) : Up.Next & M.Read}

def c.done(
  dm,
  tm,
  g,
  rs,
  only,
  ledger,
  name,
  entry,
  bin,
  hub,
  hubpa,
  hubpv,
  ds,
  ts,
  dds,
  _ss,
  _es,
  _dsy,
  _dtr,
  tts,
  _tsy,
  ig,
  _fs,
  eq,
  ek,
  hw,
  hk,
  hq,
  tw,
  tk,
  tq
):
  match dm:
    case True{}:
      Equal.cong(Up.Next, Up.Next & M.Read, x => (x, M.parse(Rend.show(M.Manifest{name, entry, bin, hub, hubpa, hubpv,
        dds, tts}))),
        view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}}, re(g, rs))),
          M1.target(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}}, g),
        c.second(g, rs, only, name, entry, bin, hub, hubpa, hubpv, dds, tts, hw, tw, c.kn(only, ds, ts, dds, tts, ek,
          hk, tk)))
    case False{}:
      match tm:
        case True{}:
          Equal.cong(Up.Next, Up.Next & M.Read, x => (x, M.parse(Rend.show(M.Manifest{name, entry, bin, hub, hubpa,
            hubpv, dds,
            tts}))),
            view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}}, re(g, rs))),
              M1.target(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, dds, tts}}, g),
            c.second(g, rs, only, name, entry, bin, hub, hubpa, hubpv, dds, tts, hw, tw,
              c.kn(only, ds, ts, dds, tts, ek, hk, tk)))
        case False{}:
          pair_eq(view(Up.next(only, M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}}, re(g, rs))),
            M1.target(M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}}, g),
            M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}},
            W.parsed(D2.ledger.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore", I.sync(dds, ig), []),
              ledger)),
            c.same(g, rs, only, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, tts, hw, tw,
              c.kn(only, ds, ts, dds, tts, ek, hk, tk), hq, tq),
            Equal.sym(M.Read,
              W.parsed(D2.ledger.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore", I.sync(dds, ig), []),
                ledger)),
              M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}},
              Equal.trans(M.Read,
                W.parsed(D2.ledger.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore",
                  I.sync(dds, ig), []), ledger)),
                W.parsed(ledger), M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}},
                Equal.cong(Maybe<&2, String>, M.Read, x => W.parsed(x),
                  D2.ledger.left(Up.edit.if(String.eq(I.sync(dds, ig), ig), ".gitignore", I.sync(dds, ig), []),
                    ledger), ledger, li(String.eq(I.sync(dds, ig), ig), I.sync(dds, ig), ledger)),
                eq)))

# LAW: the sources, once they are known
law c.srcs:
  for srcs: Up.Srcs
  for +dm: Bool
  for +tm: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Cli>
  for +tsy: List<&2, String>
  for +ig: String
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for hk: {U.known(only, dds) == U.known(only, ds) : Bool}
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for tk: {M.tool.known(only, tts) == M.tool.known(only, ts) : Bool}
  for tq: {Bool.pick(List<&2, M.Cli>, tm, ts, tts) == ts : List<&2, M.Cli>}
  for se: {String.is_empty(Up.next.stop(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
    Up.Deps{dds, ss,
      es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig))) == True{} : Bool}
  {core.lhs(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds, ss, es, dm, dsy,
    dtr, [], ""},
    Up.Tools{tts, tm, tsy, [], ""}, ig), only, g, rs) == core.rhs(Up.got.srcs(srcs, M.Manifest{name, entry, bin, hub,
      hubpa, hubpv,
      ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), g,
        ledger) : Up.Next & M.Read}

def c.srcs(
  srcs,
  dm,
  tm,
  g,
  rs,
  only,
  ledger,
  name,
  entry,
  bin,
  hub,
  hubpa,
  hubpv,
  ds,
  ts,
  dds,
  ss,
  es,
  dsy,
  dtr,
  tts,
  tsy,
  ig,
  eq,
  ek,
  hw,
  hk,
  hq,
  tw,
  tk,
  tq,
  se
):
  match srcs:
    case Up.Srcs{fs}:
      c.done(dm, tm, g, rs, only, ledger, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dsy, dtr, tts, tsy,
        ig, fs, eq,
        ek, hw, hk, hq, tw, tk, tq)
    case Up.SrcsWait{ask}:
      Eq.bit.absurd(&2, {core.lhs(Up.got.srcs(Up.SrcsWait{ask}, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), only, g, rs)
        == core.rhs(Up.got.srcs(Up.SrcsWait{ask}, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds,
          ss, es, dm,
          dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), g, ledger) : Up.Next & M.Read}, se)
    case Up.SrcsNo{+why}:
      Eq.bit.absurd(&2, {core.lhs(Up.got.srcs(Up.SrcsNo{why}, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
        Up.Deps{dds,
        ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), only, g, rs)
        == core.rhs(Up.got.srcs(Up.SrcsNo{why}, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds,
          ss, es, dm,
          dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}, ig), g, ledger) : Up.Next & M.Read},
        mv.halt_clash(why, se))

# LAW: `.gitignore`, once it is known
law c.ignore:
  for said: Up.Said
  for +srcs: Up.Srcs
  for +dm: Bool
  for +tm: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for +dds: List<&2, M.Dep>
  for +ss: List<&2, U.Swap>
  for +es: List<&2, U.Swap>
  for +dsy: List<&2, String>
  for +dtr: List<&2, Up.Laid>
  for +tts: List<&2, M.Cli>
  for +tsy: List<&2, String>
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dds) == dsettle(dds, dd.says(Up.deps.walk(re(g, rs), only,
      M.hub.or(hub), dds))) : Up.Deps}
  for hk: {U.known(only, dds) == U.known(only, ds) : Bool}
  for hq: {Bool.pick(List<&2, M.Dep>, dm, ds, dds) == ds : List<&2, M.Dep>}
  for tw: {Up.tools.walk(re(g, rs), only, tts) == tsettle(tts, tt.says(Up.tools.walk(re(g, rs), only, tts))) : Up.Tools}
  for tk: {M.tool.known(only, tts) == M.tool.known(only, ts) : Bool}
  for tq: {Bool.pick(List<&2, M.Cli>, tm, ts, tts) == ts : List<&2, M.Cli>}
  for se: {String.is_empty(Up.next.stop(Up.got.ignore(said, srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
    ts},
      Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}))) == True{} : Bool}
  {core.lhs(Up.got.ignore(said, srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds, ss, es, dm,
    dsy, dtr,
    [], ""}, Up.Tools{tts, tm, tsy, [], ""}), only, g, rs) == core.rhs(Up.got.ignore(said, srcs, M.Manifest{name,
      entry, bin, hub, hubpa, hubpv, ds, ts}, Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [],
        ""}), g,
        ledger) : Up.Next & M.Read}

def c.ignore(
  said,
  srcs,
  dm,
  tm,
  g,
  rs,
  only,
  ledger,
  name,
  entry,
  bin,
  hub,
  hubpa,
  hubpv,
  ds,
  ts,
  dds,
  ss,
  es,
  dsy,
  dtr,
  tts,
  tsy,
  eq,
  ek,
  hw,
  hk,
  hq,
  tw,
  tk,
  tq,
  se
):
  match said:
    case Up.Said{+ig}:
      c.srcs(srcs, dm, tm, g, rs, only, ledger, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dsy, dtr,
        tts, tsy, ig,
        eq, ek, hw, hk, hq, tw, tk, tq, se)
    case Up.Unsaid{+why}:
      Eq.bit.absurd(&2, {core.lhs(Up.got.ignore(Up.Unsaid{why}, srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv,
        ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), only, g, rs)
        == core.rhs(Up.got.ignore(Up.Unsaid{why}, srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
          Up.Deps{dds, ss,
          es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), g, ledger) : Up.Next & M.Read},
        mv.halt_clash(why, se))
    case Up.Unasked{ask}:
      Eq.bit.absurd(&2, {core.lhs(Up.got.ignore(Up.Unasked{ask}, srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv,
        ds, ts},
        Up.Deps{dds, ss, es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), only, g, rs)
        == core.rhs(Up.got.ignore(Up.Unasked{ask}, srcs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts},
          Up.Deps{dds, ss,
          es, dm, dsy, dtr, [], ""}, Up.Tools{tts, tm, tsy, [], ""}), g, ledger) : Up.Next & M.Read}, se)

# LAW: the walks, once they are done or refused
law c.pins:
  for dd: Up.Deps
  for tt: Up.Tools
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == True{} : Bool}
  for hw: {Up.deps.walk(re(g, rs), only, M.hub.or(hub), dd.ds(dd)) == dsettle(dd.ds(dd), dd.says(Up.deps.walk(re(g,
      rs), only, M.hub.or(hub), dd.ds(dd)))) : Up.Deps}
  for hk: {Bool.or(dunc(dd), U.known(only, dd.ds(dd))) == Bool.or(dunc(dd), U.known(only, ds)) : Bool}
  for hq: {dstay(dd, ds) == ds : List<&2, M.Dep>}
  for tw: {Up.tools.walk(re(g, rs), only, tt.ts(tt)) == tsettle(tt.ts(tt), tt.says(Up.tools.walk(re(g, rs), only,
      tt.ts(tt)))) : Up.Tools}
  for tk: {Bool.or(tunc(tt), M.tool.known(only, tt.ts(tt))) == Bool.or(tunc(tt), M.tool.known(only, ts)) : Bool}
  for tq: {tstay(tt, ts) == ts : List<&2, M.Cli>}
  for se: {String.is_empty(Up.next.stop(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
      ts}))) == True{} : Bool}
  {core.lhs(Up.pins(dd, tt, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), only, g,
    rs) == core.rhs(Up.pins(dd, tt,
    rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), g, ledger) : Up.Next & M.Read}

def c.pins(
  dd,
  tt,
  g,
  rs,
  only,
  ledger,
  name,
  entry,
  bin,
  hub,
  hubpa,
  hubpv,
  ds,
  ts,
  eq,
  ek,
  hw,
  hk,
  hq,
  tw,
  tk,
  tq,
  se
):
  match dd tt:
    case Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}} Up.Tools{tts, tm, tsy, tasks, tbad}:
      Eq.bit.absurd(&2, {core.lhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}},
          Up.Tools{tts, tm, tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), only, g,
            rs)
        == core.rhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SCon{c, cs}},
          Up.Tools{tts, tm, tsy, tasks, tbad}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), g,
            ledger) : Up.Next & M.Read}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}} Up.Tools{tts, tm, tsy, tasks, SCon{c, cs}}:
      Eq.bit.absurd(&2, {core.lhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}},
          Up.Tools{tts, tm, tsy, tasks, SCon{c, cs}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}),
            only, g, rs)
        == core.rhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, dasks, SNil{}},
          Up.Tools{tts, tm, tsy, tasks, SCon{c, cs}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), g,
            ledger) : Up.Next & M.Read}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}} Up.Tools{tts, tm, tsy, tasks, SNil{}}:
      Eq.bit.absurd(&2, {core.lhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}},
          Up.Tools{tts, tm, tsy, tasks, SNil{}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), only, g,
            rs)
        == core.rhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, a <> as, SNil{}},
          Up.Tools{tts, tm, tsy, tasks, SNil{}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), g,
            ledger) : Up.Next & M.Read}, se)
    case Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}} Up.Tools{tts, tm, tsy, a <> as, SNil{}}:
      Eq.bit.absurd(&2, {core.lhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}},
          Up.Tools{tts, tm, tsy, a <> as, SNil{}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), only,
            g, rs)
        == core.rhs(Up.pins(Up.Deps{dds, ss, es, dm, dsy, dtr, [], SNil{}},
          Up.Tools{tts, tm, tsy, a <> as, SNil{}}, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), g,
            ledger) : Up.Next & M.Read}, se)
    case Up.Deps{+dds, +ss, +es, +dm, +dsy, +dtr, [], SNil{}} Up.Tools{+tts, +tm, +tsy, [], SNil{}}:
      c.ignore(Up.text.said(rs, Up.Ignore{}), Up.ask.srcs(List.is_empty(&2, U.Swap, es), rs), dm, tm,
        g, rs, only, ledger, name, entry, bin, hub, hubpa, hubpv, ds, ts, dds, ss, es, dsy, dtr, tts, tsy,
        eq, ek, hw, hk, hq, tw, tk, tq, se)

# LAW: once `--package` is known to name something
law c.known:
  for k: Bool
  for +g: String
  for +rs: List<&2, Up.Reply>
  for +only: String
  for +ledger: Maybe<&2, String>
  for +name: String
  for +entry: String
  for +bin: String
  for +hub: String
  for +hubpa: String
  for +hubpv: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Cli>
  for eq: {W.parsed(ledger) == M.Good{M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}} : M.Read}
  for ek: {Bool.or(U.known(only, ds), M.tool.known(only, ts)) == k : Bool}
  for se: {String.is_empty(Up.next.stop(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds,
      ts}))) == True{} : Bool}
  {core.lhs(Up.known(k, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), only, g,
    rs) == core.rhs(Up.known(k,
    only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), g, ledger) : Up.Next & M.Read}

def c.known(k, g, rs, only, ledger, name, entry, bin, hub, hubpa, hubpv, ds, ts, eq, ek, se):
  match k:
    case False{}:
      Eq.bit.absurd(&2, {core.lhs(Up.known(False{}, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}),
        only, g, rs)
        == core.rhs(Up.known(False{}, only, rs, M.Manifest{name, entry, bin, hub, hubpa, hubpv, ds, ts}), g,
          ledger) : Up.Next & M.Read},
        mv.halt_clash("ez: no dependency or tool named " ++ only, se))
    case True{}:
      c.pins(Up.deps.walk(rs, only, M.hub.or(hub), ds), Up.tools.walk(rs, only, ts), g, rs, only, ledger,
        name, entry, bin, hub, hubpa, hubpv, ds, ts, eq, ek,
        w.all(g, rs, only, M.hub.or(hub), ds), kd.known(rs, only, M.hub.or(hub), ds),
        dq.all(rs, only, M.hub.or(hub), ds),
        tw.all(g, rs, only, ts), tkd.known(rs, only, ts), tq.all(rs, only, ts), se)

# LAW: an upgrade that does not stop is decided again, on the ledger it
# left, against the same remote, as its target, and its lock was made from
# the ledger it wrote, read
law core:
  for r: M.Read
  for +only: String
  for +rs: List<&2, Up.Reply>
  for +g: String
  for +ledger: Maybe<&2, String>
  for eq: {W.parsed(ledger) == r : M.Read}
  for se: {String.is_empty(Up.next.stop(Up.next(only, r, rs))) == True{} : Bool}
  {core.lhs(Up.next(only, r, rs), only, g, rs) == core.rhs(Up.next(only, r, rs), g, ledger)
    : Up.Next & M.Read}

def core(r, only, rs, g, ledger, eq, se):
  match r:
    case M.Bad{+why}:
      Equal.cong(M.Read, Up.Next & M.Read, x => (Up.plain(M.Bad{why}), x), M.Bad{why}, W.parsed(ledger),
        Equal.sym(M.Read, W.parsed(ledger), M.Bad{why}, eq))
    case M.Good{m}:
      match m:
        case M.Manifest{+name, +entry, +bin, +hub, +hubpa, +hubpv, +ds, +ts}:
          c.known(Bool.or(U.known(only, ds), M.tool.known(only, ts)), g, rs, only, ledger, name, entry,
            bin, hub, hubpa, hubpv, ds, ts, eq, {==}, se)

# ---------------------------------------------------------------------------
# the trees the lock lays are named (laws/LaidTreeNamedByManifest.bend)

# whether a verdict, laid under a hash, would be named by it: a refusal lays
# nothing, and a tree that passed is named when its files, weighed by their
# own texts, hash to it
def nv(+hash: String, v: W.Verdict) -> Bool:
  match v:
    case W.No{_why}:
      True{}
    case W.Ok{fs, ss}:
      String.eq(hash, W.named(W.laid(fs, ss)))
    case W.Named{_names}:
      True{}

# an outcome as a bit
def win(o: P.Outcome) -> Bool:
  match o:
    case P.Success{}:
      True{}
    case P.Refused{_why}:
      False{}

# the entry lookup `outcome.k` turns on
def got(+w: A.World) -> Maybe<&2, String>:
  K.look(AP.files(w), Path.norm(AP.entry(w)))

# a walk's hash and root, "" for no package
def wh(k: K.Walked) -> String:
  match k:
    case K.Walked{h, _r, _fs, _ss}:
      h
    case K.Asks{_at}:
      ""
    case K.Refused{_why}:
      ""

# the parts of what an add writes after the ledger, named
def nxt(+d: M.Dep, +m: M.Manifest, +w: A.World) -> String:
  I.sync(A.deps.of(Rend.add.keep(m, d)), A.ignore(w))

def gss(+d: M.Dep, +h: String, +m: M.Manifest) -> List<&2, String>:
  AP.gone(M.find(A.deps.of(m), M.dep.name(d)), h, A.deps.of(Rend.add.keep(m, d)))

# the dependency and the effects of the walk of an add, named
def dd(+w: A.World) -> M.Dep:
  AP.dep.of(wh(AP.walked(w)), M1.wr(AP.walked(w)), w)

# ---------------------------------------------------------------------------
# refusals after the walk

# LAW: an outcome that is no success seals a plan that refuses
law seal_refused:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for e: {win(o) == False{} : Bool}
  {AP.refuses.plan(AP.seal(es, o)) == True{} : Bool}

def seal_refused(es, o, e):
  match o:
    case P.Success{}:
      Eq.bit.absurd2(&2, {AP.refuses.plan(AP.seal(es, P.Success{})) == True{} : Bool}, e)
    case P.Refused{_why}:
      {==}

# LAW: an add whose walk ends in no success refuses, whatever the verdict
law lose_v:
  for v: AP.Verdict
  for +w: A.World
  for e: {win(AP.outcome.k(AP.walked(w), w)) == False{} : Bool}
  {AP.refuses.plan(AP.plan.v(v, w)) == True{} : Bool}

def lose_v(v, w, e):
  match v:
    case AP.Go{}:
      seal_refused(AP.effects.k(AP.walked(w), w), AP.outcome.k(AP.walked(w), w), e)
    case AP.Pending{_qs}:
      {==}
    case AP.Stop{_why}:
      {==}

# ---------------------------------------------------------------------------
# the tree laid

# a walk's package with its hash and file list made again from its texts
def fix(k: K.Walked) -> K.Walked:
  match k:
    case K.Walked{_h, +r, +fs, _ss}:
      K.Walked{K.hash_of(K.files_of(K.laid.sums(fs))), r, fs, K.files_of(K.laid.sums(fs))}
    case K.Asks{at}:
      K.Asks{at}
    case K.Refused{why}:
      K.Refused{why}

# a package's file list, weighed from its texts, and the files a `Lay`
# writes for it
def lsum(fs: List<&2, K.Source>) -> List<&2, K.Item>:
  K.files_of(K.laid.sums(fs))

def lh(fs: List<&2, K.Source>) -> String:
  K.hash_of(lsum(fs))

# ---------------------------------------------------------------------------
# a hub add that has a package

# the texts a verdict carries. Proof vocabulary.
def hvs(v: H.Verdict) -> List<&2, String>:
  match v:
    case H.Go{_h, _fs, ss}:
      ss
    case H.Pending{_asks}:
      []
    case H.Stop{_why}:
      []

# LAW: a hub verdict whose plan does not refuse is `Go`, and its plan is made
# from the package it carries
law hplan_made:
  for v: H.Verdict
  for +w: A.World
  for ok: {H.refuses.plan(H.plan.v(v, w)) == False{} : Bool}
  {H.plan.v(v, w) == H.made(H.verdict.hash(v), H.verdict.files(v), hvs(v), w) : P.Plan}

def hplan_made(v, w, ok):
  match v:
    case H.Go{_h, _fs, _ss}:
      {==}
    case H.Pending{asks}:
      Eq.bit.absurd2(&2, {H.plan.v(H.Pending{asks}, w) == H.made("", [], [], w) : P.Plan}, ok)
    case H.Stop{why}:
      Eq.bit.absurd2(&2, {H.plan.v(H.Stop{why}, w) == H.made("", [], [], w) : P.Plan}, ok)

# LAW: a sealed hub plan that does not refuse is its effects, ending in
# success
law hseal_success:
  for es: List<&2, P.Effect>
  for o: P.Outcome
  for ok: {H.refuses.plan(H.seal(es, o)) == False{} : Bool}
  {H.seal(es, o) == P.Plan{es, P.Success{}} : P.Plan}

def hseal_success(_es, o, ok):
  match o:
    case P.Success{}:
      {==}
    case P.Refused{why}:
      Eq.bit.absurd2(&2, {H.seal(_es, P.Refused{why}) == P.Plan{_es, P.Success{}} : P.Plan},
        ok)

# the plan a hub add made, and its effects, named. Proof vocabulary.
def hmade(+w: A.World) -> P.Plan:
  H.made(H.hash(w), H.files(w), hvs(H.decide(w)), w)

def heff(+w: A.World) -> List<&2, P.Effect>:
  H.effects.of(H.added(w), H.hash(w), W.laid(H.files(w), hvs(H.decide(w))),
    A.manifest.of(A.read(w)), w)

def hout(+w: A.World) -> P.Outcome:
  H.outcome.of(H.hash(w), H.files(w), w)

# LAW: a hub add that does not refuse made a plan that does not refuse
law hmade_ok:
  for +w: A.World
  for +ok: {H.refuses(w) == False{} : Bool}
  {H.refuses.plan(hmade(w)) == False{} : Bool}

def hmade_ok(w, ok):
  Equal.trans(Bool, H.refuses.plan(hmade(w)), H.refuses.plan(H.plan(w)), False{},
    Equal.cong(P.Plan, Bool, pl => H.refuses.plan(pl), hmade(w), H.plan(w),
      Equal.sym(P.Plan, H.plan(w), hmade(w), hplan_made(H.decide(w), w, ok))),
    ok)

# LAW: a hub add that does not refuse runs the effects of its package
law hsucceeds:
  for +w: A.World
  for +ok: {H.refuses(w) == False{} : Bool}
  {H.plan(w) == P.Plan{heff(w), P.Success{}} : P.Plan}

def hsucceeds(w, ok):
  Equal.trans(P.Plan, H.plan(w), hmade(w), P.Plan{heff(w), P.Success{}},
    hplan_made(H.decide(w), w, ok),
    hseal_success(heff(w), hout(w), hmade_ok(w, ok)))

# ---------------------------------------------------------------------------
# what a hub add writes

# the `.gitignore` a hub add derives, and whether it is the one there
def hnext(+w: A.World) -> String:
  I.sync(A.deps.of(Rend.add.keep(A.manifest.of(A.read(w)), H.added(w))), A.ignore(w))

def hsame(+w: A.World) -> Bool:
  String.eq(hnext(w), A.ignore(w))

# The version order. `Git.ord.ver` answers an `Ord`; read as Base's `Cmp`, each
# layer of it is a lexicographic step over a layer below, the shape
# the package walk's proofs proved consistent for strings: `tri` says a third
# comparison is one the first two leave room for, and `cmp.flip` is a
# comparison taken the other way round. Each layer gets a `Cmp` twin that
# computes on constructors, a law that the twin is the layer, and the twin's
# three facts: consistent across three versions, flipped when swapped, and
# EQ against itself. The fold's law needs exactly those: a version the fold
# passed over is below what it kept, and what it kept is below what replaced
# it, so the first is below the last.

# an order read as a comparison
def oc(o: Git.Ord) -> Cmp:
  match o:
    case Git.Lt{}:
      LT{}
    case Git.Eq{}:
      EQ{}
    case Git.Gt{}:
      GT{}

# LAW: newer is GT
law newer_gt:
  for o: Git.Ord
  {Git.newer(o) == Cmp.is_gt(oc(o)) : Bool}

def newer_gt(o):
  match o:
    case Git.Lt{}:
      {==}
    case Git.Eq{}:
      {==}
    case Git.Gt{}:
      {==}

# LAW: a lexicographic step of orders is one of comparisons
law lex_at:
  for o: Git.Ord
  for r: Git.Ord
  {cmp.lex(oc(o), oc(r)) == oc(Git.ord.nums.at(o, _u => r)) : Cmp}

def lex_at(o, _r):
  match o:
    case Git.Lt{}:
      {==}
    case Git.Eq{}:
      {==}
    case Git.Gt{}:
      {==}

# Numbers.

# LAW: two numbers compared the other way round
law nat.flip:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(b, a) == cmp.flip(Nat.cmp(a, b)) : Cmp}

def nat.flip(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nat.flip(p, q)

# LAW: three numbers compare consistently
law nat.tri:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {tri(Nat.cmp(a, b), Nat.cmp(b, c), Nat.cmp(a, c)) == True{} : Bool}

def nat.tri(a, b, c):
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      {==}
    case 0n 1n+q 1n+r:
      tri.lt.free(Nat.cmp(q, r))
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+r:
      {==}
    case 1n+p 1n+q 0n:
      tri.mid.gt(Nat.cmp(p, q), GT{})
    case 1n+p 1n+q 1n+r:
      nat.tri(p, q, r)

# LAW: the order `ord.nat` builds from a comparison is that comparison
law nat_ord.go:
  for c: Cmp
  {c == oc(Git.ord.nat(Cmp.is_eq(c), Cmp.is_lt(c))) : Cmp}

def nat_ord.go(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# LAW: and so the order of two numbers is their comparison
law nat_ord:
  for +a: Nat
  for +b: Nat
  {Nat.cmp(a, b) == oc(Git.ord.nat(Nat.is_eq(a, b), Nat.is_lt(a, b))) : Cmp}

def nat_ord(a, b):
  nat_ord.go(Nat.cmp(a, b))

# Dotted numbers. A missing part is a zero, so a list that has run out
# compares as zero against the other's head, and as nothing after it.

# the comparison of two lists of numbers, zero where one has run out
def nums.c(a: List<&2, Nat>, b: List<&2, Nat>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{+h, t}:
      cmp.lex(Nat.cmp(0n, h), nums.c([], t))
    case Con{+h, t} Nil{}:
      cmp.lex(Nat.cmp(h, 0n), nums.c(t, []))
    case Con{+ha, ta} Con{+hb, tb}:
      cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))

# LAW: one step of padding, with the rest already known
law pad.step:
  for +h: Nat
  for +t: List<&2, Nat>
  for ih: {nums.c([], t) == oc(Git.ord.pad(t)) : Cmp}
  {nums.c([], h <> t) == oc(Git.ord.pad(h <> t)) : Cmp}

def pad.step(h, _t, ih):
  match h:
    case 0n:
      ih
    case 1n+p:
      {==}

# LAW: a list against nothing is a list against zeros
law pad.c:
  for +t: List<&2, Nat>
  {nums.c([], t) == oc(Git.ord.pad(t)) : Cmp}

def pad.c(t):
  match t:
    case []:
      {==}
    case Con{+h, +r}:
      pad.step(h, r, pad.c(r))

# LAW: the same on the other side, one step
law padr.step:
  for +h: Nat
  for +t: List<&2, Nat>
  for ih: {nums.c(t, []) == oc(Git.ord.flip(Git.ord.pad(t))) : Cmp}
  {nums.c(h <> t, []) == oc(Git.ord.flip(Git.ord.pad(h <> t))) : Cmp}

def padr.step(h, _t, ih):
  match h:
    case 0n:
      ih
    case 1n+p:
      {==}

# LAW: nothing against a list is zeros against it
law padr.c:
  for +t: List<&2, Nat>
  {nums.c(t, []) == oc(Git.ord.flip(Git.ord.pad(t))) : Cmp}

def padr.c(t):
  match t:
    case []:
      {==}
    case Con{+h, +r}:
      padr.step(h, r, padr.c(r))

# LAW: the twin is `ord.nums`
law nums.is:
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  {nums.c(a, b) == oc(Git.ord.nums(a, b)) : Cmp}

def nums.is(a, b):
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+h, +t}:
      pad.c(h <> t)
    case Con{+h, +t} Nil{}:
      padr.c(h <> t)
    case Con{+ha, +ta} Con{+hb, +tb}:
      %lex_at(Git.ord.nat(Nat.is_eq(ha, hb), Nat.is_lt(ha, hb)), Git.ord.nums(ta, tb))
        : {nums.c(ha <> ta, hb <> tb) == _ : Cmp}
      %nat_ord(ha, hb) : {cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))
        == cmp.lex(_, oc(Git.ord.nums(ta, tb))) : Cmp}
      %nums.is(ta, tb) : {cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))
        == cmp.lex(Nat.cmp(ha, hb), _) : Cmp}
      {==}

# LAW: dotted numbers compared the other way round
law nums.flip:
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  {nums.c(b, a) == cmp.flip(nums.c(a, b)) : Cmp}

def nums.flip(a, b):
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+h, +t}:
      %Equal.sym(Cmp, Nat.cmp(h, 0n), cmp.flip(Nat.cmp(0n, h)), nat.flip(0n, h))
        : {cmp.lex(_, nums.c(t, [])) == cmp.flip(
        cmp.lex(Nat.cmp(0n, h), nums.c([], t))) : Cmp}
      %Equal.sym(Cmp, nums.c(t, []), cmp.flip(nums.c([], t)), nums.flip([], t))
        : {cmp.lex(cmp.flip(Nat.cmp(0n, h)), _)
        == cmp.flip(cmp.lex(Nat.cmp(0n, h), nums.c([], t))) : Cmp}
      lex.flip(Nat.cmp(0n, h), nums.c([], t))
    case Con{+h, +t} Nil{}:
      %Equal.sym(Cmp, Nat.cmp(0n, h), cmp.flip(Nat.cmp(h, 0n)), nat.flip(h, 0n))
        : {cmp.lex(_, nums.c([], t)) == cmp.flip(
        cmp.lex(Nat.cmp(h, 0n), nums.c(t, []))) : Cmp}
      %Equal.sym(Cmp, nums.c([], t), cmp.flip(nums.c(t, [])), nums.flip(t, []))
        : {cmp.lex(cmp.flip(Nat.cmp(h, 0n)), _)
        == cmp.flip(cmp.lex(Nat.cmp(h, 0n), nums.c(t, []))) : Cmp}
      lex.flip(Nat.cmp(h, 0n), nums.c(t, []))
    case Con{+ha, +ta} Con{+hb, +tb}:
      %Equal.sym(Cmp, Nat.cmp(hb, ha), cmp.flip(Nat.cmp(ha, hb)), nat.flip(ha, hb))
        : {cmp.lex(_, nums.c(tb, ta)) == cmp.flip(
        cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))) : Cmp}
      %Equal.sym(Cmp, nums.c(tb, ta), cmp.flip(nums.c(ta, tb)), nums.flip(ta, tb))
        : {cmp.lex(cmp.flip(Nat.cmp(ha, hb)), _)
        == cmp.flip(cmp.lex(Nat.cmp(ha, hb), nums.c(ta, tb))) : Cmp}
      lex.flip(Nat.cmp(ha, hb), nums.c(ta, tb))

# LAW: three lists of dotted numbers compare consistently. A list that has
# run out stands in as a zero and nothing after it, which is why every arm
# is the same lexicographic step.
law nums.tri:
  for +a: List<&2, Nat>
  for +b: List<&2, Nat>
  for +c: List<&2, Nat>
  {tri(nums.c(a, b), nums.c(b, c), nums.c(a, c)) == True{} : Bool}

def nums.tri(a, b, c):
  match a b c:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{+hc, +tc}:
      lex.tri(Nat.cmp(0n, 0n), Nat.cmp(0n, hc), Nat.cmp(0n, hc),
        nums.c([], []), nums.c([], tc), nums.c([], tc),
        nat.tri(0n, 0n, hc), nums.tri([], [], tc))
    case Nil{} Con{+hb, +tb} Nil{}:
      lex.tri(Nat.cmp(0n, hb), Nat.cmp(hb, 0n), Nat.cmp(0n, 0n),
        nums.c([], tb), nums.c(tb, []), nums.c([], []),
        nat.tri(0n, hb, 0n), nums.tri([], tb, []))
    case Nil{} Con{+hb, +tb} Con{+hc, +tc}:
      lex.tri(Nat.cmp(0n, hb), Nat.cmp(hb, hc), Nat.cmp(0n, hc),
        nums.c([], tb), nums.c(tb, tc), nums.c([], tc),
        nat.tri(0n, hb, hc), nums.tri([], tb, tc))
    case Con{+ha, +ta} Nil{} Nil{}:
      lex.tri(Nat.cmp(ha, 0n), Nat.cmp(0n, 0n), Nat.cmp(ha, 0n),
        nums.c(ta, []), nums.c([], []), nums.c(ta, []),
        nat.tri(ha, 0n, 0n), nums.tri(ta, [], []))
    case Con{+ha, +ta} Nil{} Con{+hc, +tc}:
      lex.tri(Nat.cmp(ha, 0n), Nat.cmp(0n, hc), Nat.cmp(ha, hc),
        nums.c(ta, []), nums.c([], tc), nums.c(ta, tc),
        nat.tri(ha, 0n, hc), nums.tri(ta, [], tc))
    case Con{+ha, +ta} Con{+hb, +tb} Nil{}:
      lex.tri(Nat.cmp(ha, hb), Nat.cmp(hb, 0n), Nat.cmp(ha, 0n),
        nums.c(ta, tb), nums.c(tb, []), nums.c(ta, []),
        nat.tri(ha, hb, 0n), nums.tri(ta, tb, []))
    case Con{+ha, +ta} Con{+hb, +tb} Con{+hc, +tc}:
      lex.tri(Nat.cmp(ha, hb), Nat.cmp(hb, hc), Nat.cmp(ha, hc),
        nums.c(ta, tb), nums.c(tb, tc), nums.c(ta, tc),
        nat.tri(ha, hb, hc), nums.tri(ta, tb, tc))

# Pre-release identifiers: a number below a word, numbers by value, words by
# Base's string order.

# the comparison of two identifiers
def id.c(x: Git.Id, y: Git.Id) -> Cmp:
  match x y:
    case Git.IdNum{+n} Git.IdNum{+m}:
      Nat.cmp(n, m)
    case Git.IdNum{_n} Git.IdWord{_s}:
      LT{}
    case Git.IdWord{_s} Git.IdNum{_n}:
      GT{}
    case Git.IdWord{+s} Git.IdWord{+t}:
      String.order(s, t)

# LAW: and the same for a comparison alone, which is what Base's String.order
# answers
law str_ord.cmp:
  for c: Cmp
  {c == oc(Git.ord.str(Cmp.is_eq(c), Cmp.is_le(c))) : Cmp}

def str_ord.cmp(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# LAW: the twin is `ord.id`
law id.is:
  for +x: Git.Id
  for +y: Git.Id
  {id.c(x, y) == oc(Git.ord.id(x, y)) : Cmp}

def id.is(x, y):
  match x y:
    case Git.IdNum{+n} Git.IdNum{+m}:
      nat_ord(n, m)
    case Git.IdNum{_n} Git.IdWord{_s}:
      {==}
    case Git.IdWord{_s} Git.IdNum{_n}:
      {==}
    case Git.IdWord{+s} Git.IdWord{+t}:
      str_ord.cmp(String.order(s, t))

# LAW: two identifiers compared the other way round
law id.flip:
  for +x: Git.Id
  for +y: Git.Id
  {id.c(y, x) == cmp.flip(id.c(x, y)) : Cmp}

def id.flip(x, y):
  match x y:
    case Git.IdNum{+n} Git.IdNum{+m}:
      nat.flip(n, m)
    case Git.IdNum{_n} Git.IdWord{_s}:
      {==}
    case Git.IdWord{_s} Git.IdNum{_n}:
      {==}
    case Git.IdWord{+s} Git.IdWord{+t}:
      str.flip(s, t)

# LAW: three identifiers compare consistently
law id.tri:
  for +x: Git.Id
  for +y: Git.Id
  for +z: Git.Id
  {tri(id.c(x, y), id.c(y, z), id.c(x, z)) == True{} : Bool}

def id.tri(x, y, z):
  match x y z:
    case Git.IdNum{+a} Git.IdNum{+b} Git.IdNum{+c}:
      nat.tri(a, b, c)
    case Git.IdNum{+a} Git.IdNum{+b} Git.IdWord{_c}:
      tri.free.lt(Nat.cmp(a, b))
    case Git.IdNum{_a} Git.IdWord{_b} Git.IdNum{_c}:
      {==}
    case Git.IdNum{_a} Git.IdWord{+b} Git.IdWord{+c}:
      tri.lt.free(String.order(b, c))
    case Git.IdWord{_a} Git.IdNum{_b} Git.IdNum{_c}:
      {==}
    case Git.IdWord{_a} Git.IdNum{_b} Git.IdWord{_c}:
      {==}
    case Git.IdWord{+a} Git.IdWord{+b} Git.IdNum{_c}:
      tri.mid.gt(String.order(a, b), GT{})
    case Git.IdWord{+a} Git.IdWord{+b} Git.IdWord{+c}:
      str.tri(a, b, c)

# A pre-release's identifiers, one at a time; a list that runs out first is
# the lesser.

# the comparison of two lists of identifiers
def ids.c(xs: List<&2, Git.Id>, ys: List<&2, Git.Id>) -> Cmp:
  match xs ys:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{_h, _t}:
      LT{}
    case Con{_h, _t} Nil{}:
      GT{}
    case Con{+ha, ta} Con{+hb, tb}:
      cmp.lex(id.c(ha, hb), ids.c(ta, tb))

# LAW: the twin is `ord.ids`
law ids.is:
  for +xs: List<&2, Git.Id>
  for +ys: List<&2, Git.Id>
  {ids.c(xs, ys) == oc(Git.ord.ids(xs, ys)) : Cmp}

def ids.is(xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{_h, _t}:
      {==}
    case Con{_h, _t} Nil{}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb}:
      %lex_at(Git.ord.id(ha, hb), Git.ord.ids(ta, tb))
        : {ids.c(ha <> ta, hb <> tb) == _ : Cmp}
      %id.is(ha, hb) : {cmp.lex(id.c(ha, hb), ids.c(ta, tb))
        == cmp.lex(_, oc(Git.ord.ids(ta, tb))) : Cmp}
      %ids.is(ta, tb) : {cmp.lex(id.c(ha, hb), ids.c(ta, tb))
        == cmp.lex(id.c(ha, hb), _) : Cmp}
      {==}

# LAW: identifier lists compared the other way round
law ids.flip:
  for +xs: List<&2, Git.Id>
  for +ys: List<&2, Git.Id>
  {ids.c(ys, xs) == cmp.flip(ids.c(xs, ys)) : Cmp}

def ids.flip(xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{_h, _t}:
      {==}
    case Con{_h, _t} Nil{}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb}:
      %Equal.sym(Cmp, id.c(hb, ha), cmp.flip(id.c(ha, hb)), id.flip(ha, hb))
        : {cmp.lex(_, ids.c(tb, ta)) == cmp.flip(
          cmp.lex(id.c(ha, hb), ids.c(ta, tb))) : Cmp}
      %Equal.sym(Cmp, ids.c(tb, ta), cmp.flip(ids.c(ta, tb)), ids.flip(ta, tb))
        : {cmp.lex(cmp.flip(id.c(ha, hb)), _) == cmp.flip(
          cmp.lex(id.c(ha, hb), ids.c(ta, tb))) : Cmp}
      lex.flip(id.c(ha, hb), ids.c(ta, tb))

# LAW: three identifier lists compare consistently
law ids.tri:
  for +xs: List<&2, Git.Id>
  for +ys: List<&2, Git.Id>
  for +zs: List<&2, Git.Id>
  {tri(ids.c(xs, ys), ids.c(ys, zs), ids.c(xs, zs)) == True{} : Bool}

def ids.tri(xs, ys, zs):
  match xs ys zs:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{_hc, _tc}:
      {==}
    case Nil{} Con{_hb, _tb} Nil{}:
      {==}
    case Nil{} Con{+hb, +tb} Con{+hc, +tc}:
      tri.lt.free(ids.c(hb <> tb, hc <> tc))
    case Con{_ha, _ta} Nil{} Nil{}:
      {==}
    case Con{_ha, _ta} Nil{} Con{_hc, _tc}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb} Nil{}:
      tri.mid.gt(ids.c(ha <> ta, hb <> tb), GT{})
    case Con{+ha, +ta} Con{+hb, +tb} Con{+hc, +tc}:
      lex.tri(id.c(ha, hb), id.c(hb, hc), id.c(ha, hc),
        ids.c(ta, tb), ids.c(tb, tc), ids.c(ta, tc),
        id.tri(ha, hb, hc), ids.tri(ta, tb, tc))

# A release, with no identifiers, is above every pre-release of it.

# the comparison of two pre-releases, the empty one a release
def rel.c(p: List<&2, Git.Id>, q: List<&2, Git.Id>) -> Cmp:
  match p q:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{_h, _t}:
      GT{}
    case Con{_h, _t} Nil{}:
      LT{}
    case Con{+ha, +ta} Con{+hb, +tb}:
      ids.c(ha <> ta, hb <> tb)

# LAW: the twin is `ord.rel`
law rel.is:
  for +p: List<&2, Git.Id>
  for +q: List<&2, Git.Id>
  {rel.c(p, q) == oc(Git.ord.rel(p, q)) : Cmp}

def rel.is(p, q):
  match p q:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{_h, _t}:
      {==}
    case Con{_h, _t} Nil{}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb}:
      ids.is(ha <> ta, hb <> tb)

# LAW: pre-releases compared the other way round
law rel.flip:
  for +p: List<&2, Git.Id>
  for +q: List<&2, Git.Id>
  {rel.c(q, p) == cmp.flip(rel.c(p, q)) : Cmp}

def rel.flip(p, q):
  match p q:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{_h, _t}:
      {==}
    case Con{_h, _t} Nil{}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb}:
      ids.flip(ha <> ta, hb <> tb)

# LAW: three pre-releases compare consistently
law rel.tri:
  for +p: List<&2, Git.Id>
  for +q: List<&2, Git.Id>
  for +r: List<&2, Git.Id>
  {tri(rel.c(p, q), rel.c(q, r), rel.c(p, r)) == True{} : Bool}

def rel.tri(p, q, r):
  match p q r:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{_hc, _tc}:
      {==}
    case Nil{} Con{_hb, _tb} Nil{}:
      {==}
    case Nil{} Con{_hb, _tb} Con{_hc, _tc}:
      {==}
    case Con{_ha, _ta} Nil{} Nil{}:
      {==}
    case Con{_ha, _ta} Nil{} Con{_hc, _tc}:
      {==}
    case Con{+ha, +ta} Con{+hb, +tb} Nil{}:
      tri.free.lt(ids.c(ha <> ta, hb <> tb))
    case Con{+ha, +ta} Con{+hb, +tb} Con{+hc, +tc}:
      ids.tri(ha <> ta, hb <> tb, hc <> tc)

# A version: its numbers, and its pre-release where they tie.

# the comparison of two versions, each given as its numbers and pre-release
def ver.c(na: List<&2, Nat>, pa: List<&2, Git.Id>, nb: List<&2, Nat>, pb: List<&2, Git.Id>) -> Cmp:
  cmp.lex(nums.c(na, nb), rel.c(pa, pb))

# LAW: the twin is `ord.ver` of two semver-ish versions
law ver.is:
  for +na: List<&2, Nat>
  for +pa: List<&2, Git.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, Git.Id>
  {ver.c(na, pa, nb, pb) == oc(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nb, pb})) : Cmp}

def ver.is(na, pa, nb, pb):
  %lex_at(Git.ord.nums(na, nb), Git.ord.rel(pa, pb))
    : {ver.c(na, pa, nb, pb) == _ : Cmp}
  %nums.is(na, nb) : {cmp.lex(nums.c(na, nb), rel.c(pa, pb))
    == cmp.lex(_, oc(Git.ord.rel(pa, pb))) : Cmp}
  %rel.is(pa, pb) : {cmp.lex(nums.c(na, nb), rel.c(pa, pb))
    == cmp.lex(nums.c(na, nb), _) : Cmp}
  {==}

# LAW: versions compared the other way round
law ver.flip:
  for +na: List<&2, Nat>
  for +pa: List<&2, Git.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, Git.Id>
  {ver.c(nb, pb, na, pa) == cmp.flip(ver.c(na, pa, nb, pb)) : Cmp}

def ver.flip(na, pa, nb, pb):
  %Equal.sym(Cmp, nums.c(nb, na), cmp.flip(nums.c(na, nb)), nums.flip(na, nb))
    : {cmp.lex(_, rel.c(pb, pa))
      == cmp.flip(cmp.lex(nums.c(na, nb), rel.c(pa, pb))) : Cmp}
  %Equal.sym(Cmp, rel.c(pb, pa), cmp.flip(rel.c(pa, pb)), rel.flip(pa, pb))
    : {cmp.lex(cmp.flip(nums.c(na, nb)), _)
      == cmp.flip(cmp.lex(nums.c(na, nb), rel.c(pa, pb))) : Cmp}
  lex.flip(nums.c(na, nb), rel.c(pa, pb))

# LAW: three versions compare consistently
law ver.tri:
  for +na: List<&2, Nat>
  for +pa: List<&2, Git.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, Git.Id>
  for +nc: List<&2, Nat>
  for +pc: List<&2, Git.Id>
  {tri(ver.c(na, pa, nb, pb), ver.c(nb, pb, nc, pc), ver.c(na, pa, nc, pc))
    == True{} : Bool}

def ver.tri(na, pa, nb, pb, nc, pc):
  lex.tri(nums.c(na, nb), nums.c(nb, nc), nums.c(na, nc),
    rel.c(pa, pb), rel.c(pb, pc), rel.c(pa, pc),
    nums.tri(na, nb, nc), rel.tri(pa, pb, pc))

# From comparisons back to `newer`, which is what the folds ask.

# LAW: one semver-ish version newer than another is the twin answering GT
law newer_ver:
  for +na: List<&2, Nat>
  for +pa: List<&2, Git.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, Git.Id>
  {Git.newer(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nb, pb}))
    == Cmp.is_gt(ver.c(na, pa, nb, pb)) : Bool}

def newer_ver(na, pa, nb, pb):
  %Equal.sym(Cmp, ver.c(na, pa, nb, pb),
    oc(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nb, pb})), ver.is(na, pa, nb, pb))
    : {Git.newer(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nb, pb})) == Cmp.is_gt(_) : Bool}
  newer_gt(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nb, pb}))

# LAW: what is not above c, where b is above c, is not above b. With the
# middle taken the other way round, this is `tri` read at the one row that
# matters.
law below.go:
  for u: Cmp
  for y: Cmp
  for w: Cmp
  for t: {tri(u, cmp.flip(y), w) == True{} : Bool}
  for eu: {Cmp.is_gt(u) == False{} : Bool}
  for ey: {Cmp.is_gt(y) == True{} : Bool}
  {Cmp.is_gt(w) == False{} : Bool}

def below.go(u, y, w, t, eu, ey):
  match u y:
    case LT{} GT{}:
      match w:
        case LT{}:
          {==}
        case EQ{}:
          Eq.bit.absurd(&2, {Cmp.is_gt(EQ{}) == False{} : Bool}, t)
        case GT{}:
          Eq.bit.absurd(&2, {Cmp.is_gt(GT{}) == False{} : Bool}, t)
    case EQ{} GT{}:
      match w:
        case LT{}:
          {==}
        case EQ{}:
          Eq.bit.absurd(&2, {Cmp.is_gt(EQ{}) == False{} : Bool}, t)
        case GT{}:
          Eq.bit.absurd(&2, {Cmp.is_gt(GT{}) == False{} : Bool}, t)
    case LT{} LT{}:
      Eq.bit.absurd(&2, {Cmp.is_gt(w) == False{} : Bool}, ey)
    case LT{} EQ{}:
      Eq.bit.absurd(&2, {Cmp.is_gt(w) == False{} : Bool}, ey)
    case EQ{} LT{}:
      Eq.bit.absurd(&2, {Cmp.is_gt(w) == False{} : Bool}, ey)
    case EQ{} EQ{}:
      Eq.bit.absurd(&2, {Cmp.is_gt(w) == False{} : Bool}, ey)
    case GT{} _:
      Eq.bit.absurd2(&2, {Cmp.is_gt(w) == False{} : Bool}, eu)

# LAW: the key lemma. A version not newer than c, where b is newer than c, is
# not newer than b: the order is transitive, so a fold that replaces c by b
# keeps every version it passed below what it holds.
law ver.below:
  for +na: List<&2, Nat>
  for +pa: List<&2, Git.Id>
  for +nb: List<&2, Nat>
  for +pb: List<&2, Git.Id>
  for +nc: List<&2, Nat>
  for +pc: List<&2, Git.Id>
  for ea: {Git.newer(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nc, pc})) == False{} : Bool}
  for eb: {Git.newer(Git.ord.ver(Git.Yes{nb, pb}, Git.Yes{nc, pc})) == True{} : Bool}
  {Git.newer(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nb, pb})) == False{} : Bool}

def ver.below(na, pa, nb, pb, nc, pc, ea, eb):
  %Equal.sym(Bool, Git.newer(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nb, pb})),
    Cmp.is_gt(ver.c(na, pa, nb, pb)), newer_ver(na, pa, nb, pb))
    : {_ == False{} : Bool}
  below.go(ver.c(na, pa, nc, pc), ver.c(nb, pb, nc, pc), ver.c(na, pa, nb, pb),
    Equal.trans(Bool,
      tri(ver.c(na, pa, nc, pc), cmp.flip(ver.c(nb, pb, nc, pc)),
        ver.c(na, pa, nb, pb)),
      tri(ver.c(na, pa, nc, pc), ver.c(nc, pc, nb, pb),
        ver.c(na, pa, nb, pb)),
      True{},
      Equal.cong(Cmp, Bool,
        x => tri(ver.c(na, pa, nc, pc), x, ver.c(na, pa, nb, pb)),
        cmp.flip(ver.c(nb, pb, nc, pc)), ver.c(nc, pc, nb, pb),
        Equal.sym(Cmp, ver.c(nc, pc, nb, pb), cmp.flip(ver.c(nb, pb, nc, pc)),
          ver.flip(nb, pb, nc, pc))),
      ver.tri(na, pa, nc, pc, nb, pb)),
    Equal.trans(Bool, Cmp.is_gt(ver.c(na, pa, nc, pc)),
      Git.newer(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nc, pc})), False{},
      Equal.sym(Bool, Git.newer(Git.ord.ver(Git.Yes{na, pa}, Git.Yes{nc, pc})),
        Cmp.is_gt(ver.c(na, pa, nc, pc)), newer_ver(na, pa, nc, pc)),
      ea),
    Equal.trans(Bool, Cmp.is_gt(ver.c(nb, pb, nc, pc)),
      Git.newer(Git.ord.ver(Git.Yes{nb, pb}, Git.Yes{nc, pc})), True{},
      Equal.sym(Bool, Git.newer(Git.ord.ver(Git.Yes{nb, pb}, Git.Yes{nc, pc})),
        Cmp.is_gt(ver.c(nb, pb, nc, pc)), newer_ver(nb, pb, nc, pc)),
      eb))

# The folds. Both run from the right and hold the greatest name so far; a
# name is weighed against it by `latest.have`, which the release fold shares.
# A tag `n` sits somewhere in `xs ++ [n] ++ ys`: the folds meet `ys` first,
# then `n`, which the fold takes or passes over for something not below it,
# then each of `xs`, which only ever replaces what it holds with something
# newer. `ver.below` carries `n` across each replacement.

# a version clash: nothing is both a tag and not one
def ver.emp(v: Git.Ver) -> Type:
  match v:
    case Git.No{}:
      Unit
    case Git.Yes{_ns, _ps}:
      Empty

def ver.clash(
  -ns: List<&2, Nat>,
  -ps: List<&2, Git.Id>,
  eq: {Git.No{} == Git.Yes{ns, ps} : Git.Ver}
) -> Empty:
  %eq : ver.emp(_)
  Unit{}

# LAW: a semver-ish tag has a name
law named:
  for +n: String
  for ns: List<&2, Nat>
  for ps: List<&2, Git.Id>
  for ev: {Git.ver.of(n) == Git.Yes{ns, ps} : Git.Ver}
  {String.is_empty(n) == False{} : Bool}

def named(n, ns, ps, ev):
  match n:
    case SNil{}:
      Eq.bit.gone(&2, {String.is_empty(SNil{}) == False{} : Bool},
        ver.clash(ns, ps, ev))
    case SCon{_c, _t}:
      {==}

# LAW: and exits 1, starting nothing
law quiet_exit:
  for v: TP.Verdict
  for +w: TW.World
  for r: {TP.refuses.plan(TP.plan.v(v, w)) == True{} : Bool}
  {TP.exit(TP.plan.v(v, w)) == TP.Refusal{} : TP.Exit}

def quiet_exit(v, w, r):
  match v:
    case TP.Go{}:
      Eq.bit.absurd(&2, {TP.exit(TP.plan.v(TP.Go{}, w)) == TP.Refusal{} : TP.Exit}, r)
    case TP.Pending{_as, _us}:
      {==}
    case TP.Stop{_why}:
      {==}

def L6.tool_refusal_exits_one(w, r):
  quiet_exit(TP.decide(w), w, r)

# ---------------------------------------------------------------------------
# a plan that does not refuse

# LAW: a verdict whose plan does not refuse is `Go`, and its plan is `made`
law plan_made_tool:
  for v: TP.Verdict
  for +w: TW.World
  for ok: {TP.refuses.plan(TP.plan.v(v, w)) == False{} : Bool}
  {TP.plan.v(v, w) == TP.made(w) : TP.Plan}

def plan_made_tool(v, w, ok):
  match v:
    case TP.Go{}:
      {==}
    case TP.Pending{as, us}:
      Eq.bit.absurd2(&2, {TP.plan.v(TP.Pending{as, us}, w) == TP.made(w) : TP.Plan}, ok)
    case TP.Stop{why}:
      Eq.bit.absurd2(&2, {TP.plan.v(TP.Stop{why}, w) == TP.made(w) : TP.Plan}, ok)

# LAW: so a command that does not refuse runs `made`
law made_of:
  for +w: TW.World
  for ok: {TP.refuses(w) == False{} : Bool}
  {TP.plan(w) == TP.made(w) : TP.Plan}

def made_of(w, ok):
  plan_made_tool(TP.decide(w), w, ok)

# LAW: the link a linking act writes, once the act is known
law link_of:
  for a: TW.Act
  for +w: TW.World
  for +d: String
  for l: {TP.links.act(a) == True{} : Bool}
  for got: {TW.bin.of(TW.env(w)) == Some{d} : Maybe<&2, String>}
  {TP.link.at(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(a, w), P.Success{}})
    == d ++ "/" ++ TP.name(w) : String}

def link_of(a, w, d, l, got):
  match a:
    case TW.Run{args}:
      Eq.bit.absurd(&2, {TP.link.at(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(TW.Run{args}, w),
        P.Success{}}) == d ++ "/" ++ TP.name(w) : String}, l)
    case TW.Install{}:
      %Equal.sym(Maybe<&2, String>, TW.bin.of(TW.env(w)), Some{d}, got)
        : {TW.text.or(_) ++ "/" ++ TP.name(w) == d ++ "/" ++ TP.name(w) : String}
      {==}
    case TW.Upgrade{}:
      %Equal.sym(Maybe<&2, String>, TW.bin.of(TW.env(w)), Some{d}, got)
        : {TW.text.or(_) ++ "/" ++ TP.name(w) == d ++ "/" ++ TP.name(w) : String}
      {==}

# LAW: the link `made` writes
law link_made:
  for +w: TW.World
  for a: TW.Act
  for +d: String
  for act: {TW.act(w) == a : TW.Act}
  for l: {TP.links.act(a) == True{} : Bool}
  for got: {TW.bin.of(TW.env(w)) == Some{d} : Maybe<&2, String>}
  {TP.link.at(TP.made(w)) == d ++ "/" ++ TP.name(w) : String}

def link_made(w, a, d, act, l, got):
  %Equal.sym(TW.Act, TW.act(w), a, act)
    : {TP.link.at(TP.Plan{TP.lay(w), TP.make(w), TP.finish.of(_, w), P.Success{}})
      == d ++ "/" ++ TP.name(w) : String}
  link_of(a, w, d, l, got)

law miss_made:
  for +w: TW.World
  for miss: {TP.reuse(w) == False{} : Bool}
  {TP.builds(TP.made(w)) == True{} : Bool}

def miss_made(w, miss):
  %Equal.sym(Bool, TP.reuse(w), False{}, miss) : {TP.makes(TP.make.of(_, w)) == True{} : Bool}
  {==}

def L5.tool_builds_on_miss(w, ok, miss):
  Equal.trans(Bool, TP.builds(TP.plan(w)), TP.builds(TP.made(w)), True{},
    Equal.cong(TP.Plan, Bool, pl => TP.builds(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
    miss_made(w, miss))

# ---------------------------------------------------------------------------
# laws/ToolRunExitsWithProgram.bend and laws/ToolLinkNeverRuns.bend

# LAW: `made` for `run` ends with the program and the words it was given
law run_made:
  for +w: TW.World
  for +args: List<&2, String>
  for act: {TW.act(w) == TW.Run{args} : TW.Act}
  {TP.exit(TP.made(w)) == TP.Exits{TP.out(w), args} : TP.Exit}

def run_made(w, args, act):
  %Equal.sym(TW.Act, TW.act(w), TW.Run{args}, act)
    : {TP.exit.of(TP.finish.of(_, w)) == TP.Exits{TP.out(w), args} : TP.Exit}
  {==}

def L6.tool_run_exits_with_program(w, args, act, ok):
  Equal.trans(TP.Exit, TP.exit(TP.plan(w)), TP.exit(TP.made(w)), TP.Exits{TP.out(w), args},
    Equal.cong(TP.Plan, TP.Exit, pl => TP.exit(pl), TP.plan(w), TP.made(w), made_of(w, ok)),
    run_made(w, args, act))

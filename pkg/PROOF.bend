# pkg: the proofs. `bend PROOF.bend` is the gate.
#
# The long half of this file is the order-independence of `manifest_of`: that
# a package renders the same manifest, and so is published under the same
# `0x` name, whatever order its files were found in. It was out of reach while
# the sort was Base's `List.sort`; it is reachable now that it is this
# project's own `file.sort`, and what it wanted was a permutation lemma over
# `file.ins`. That lemma needs the order files are sorted by to be a total
# order — one way round or the other, never both, and transitive — which is a
# fact about Base's `String.is_le` that Base does not state, so the walk down
# to `Word.cmp` is proved here too. `tests/publish.sh` still pins ez's answer
# against a real `bend --publish`; it is no longer the only thing holding this
# end down.
import Base
import ./pkg.bend as P
import ../check/eq.bend as Eq
import ./path.bend as Path
import ../sha/sha.bend as Sha
import ./LAWS.bend as Laws

# LAW: one step of the deduplication, with the branch the pick takes given as
# a parameter and the equation that put it there given alongside, since a
# match may not scrutinise a computed value
law dedup_dup.arm:
  for +f: P.File
  for b: P.File
  for t: List<&2, P.File>
  for bb: Bool
  for eb: {String.eq(P.file.at(f), P.file.at(b)) == bb : Bool}
  {P.dedup.head(f, P.dedup.pick(bb, f, b <> t)) == P.dedup.pick(bb, f, b <> t)
    : List<&2, P.File>}

def dedup_dup.arm(f, b, t, bb, eb):
  match bb:
    case True{}:
      Equal.cong(Bool, List<&2, P.File>, x => P.dedup.pick(x, f, b <> t),
        String.eq(P.file.at(f), P.file.at(b)), True{}, eb)
    case False{}:
      Equal.cong(Bool, List<&2, P.File>,
        x => P.dedup.pick(x, f, f <> (b <> t)),
        String.eq(P.file.at(f), P.file.at(f)), True{},
        Eq.string_eq_self(P.file.at(f)))

# LAW: offering the same file to a deduplicated list twice changes nothing
law dedup_dup.head:
  for +f: P.File
  for r: List<&2, P.File>
  {P.dedup.head(f, P.dedup.head(f, r)) == P.dedup.head(f, r)
    : List<&2, P.File>}

def dedup_dup.head(f, r):
  match r:
    case []:
      Equal.cong(Bool, List<&2, P.File>, x => P.dedup.pick(x, f, [f]),
        String.eq(P.file.at(f), P.file.at(f)), True{},
        Eq.string_eq_self(P.file.at(f)))
    case +b <> t:
      dedup_dup.arm(f, b, t, String.eq(P.file.at(f), P.file.at(b)), {==})

def Laws.dedup_dup(f, t):
  dedup_dup.head(f, P.dedup(t))

# LAW: whichever branch the pick takes, what comes back is a file and a rest
law dedup_keeps.arm:
  for -f: P.File
  for -b: P.File
  for -t: List<&2, P.File>
  for bb: Bool
  {List.is_empty(&2, P.File, P.dedup.pick(bb, f, b <> t)) == False{} : Bool}

def dedup_keeps.arm(f, b, t, bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a file offered to any deduplicated list comes back with it
law dedup_keeps.head:
  for +h: P.File
  for r: List<&2, P.File>
  {List.is_empty(&2, P.File, P.dedup.head(h, r)) == False{} : Bool}

def dedup_keeps.head(h, r):
  match r:
    case []:
      {==}
    case +b <> t:
      dedup_keeps.arm(h, b, t, String.eq(P.file.at(h), P.file.at(b)))

def Laws.dedup_keeps(h, t):
  dedup_keeps.head(h, P.dedup(t))

# LAW: the walk carries a component only until another follows it
law base_last.go:
  for ps: List<&2, String>
  for +h: String
  for +x: String
  {Path.base.go(List.append(&2, String, ps, [x]), h) == x : String}

def base_last.go(ps, h, x):
  match ps:
    case []:
      {==}
    case +a <> t:
      base_last.go(t, a, x)

def Laws.base_last(ps, x):
  match ps:
    case []:
      {==}
    case +h <> t:
      base_last.go(t, h, x)

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

# a bit is one thing or the other, never both
def bit.emp(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def bit.clash(e: {False{} == True{} : Bool}) -> Empty:
  %e : bit.emp(_)
  Unit{}

def bit.gone(a, -A: Kind(a), e: Empty) -> A:
  match e:

def bit.absurd(a, -A: Kind(a), e: {False{} == True{} : Bool}) -> A:
  bit.gone(a, A, bit.clash(e))

def bit.emp2(b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def bit.clash2(e: {True{} == False{} : Bool}) -> Empty:
  %e : bit.emp2(_)
  Unit{}

def bit.absurd2(a, -A: Kind(a), e: {True{} == False{} : Bool}) -> A:
  bit.gone(a, A, bit.clash2(e))

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

def tri.mid.gt(x, z):
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
          bit.absurd(&2, {Cmp.is_lt(Bool.cmp(ab, cb)) == True{} : Bool}, ok)
        case GT{}:
          ok
    case LT{} EQ{}:
      match z:
        case LT{}:
          tri.lt.free(Bool.cmp(bb, cb))
        case EQ{}:
          bit.absurd(&2,
            {tri(LT{}, Bool.cmp(bb, cb), Bool.cmp(ab, cb)) == True{} : Bool},
            ok)
        case GT{}:
          bit.absurd(&2,
            {tri(LT{}, Bool.cmp(bb, cb), GT{}) == True{} : Bool}, ok)
    case EQ{} LT{}:
      match z:
        case LT{}:
          tri.free.lt(Bool.cmp(ab, bb))
        case EQ{}:
          bit.absurd(&2,
            {tri(Bool.cmp(ab, bb), LT{}, Bool.cmp(ab, cb)) == True{} : Bool},
            ok)
        case GT{}:
          bit.absurd(&2,
            {tri(Bool.cmp(ab, bb), LT{}, GT{}) == True{} : Bool}, ok)
    case EQ{} EQ{}:
      match z:
        case LT{}:
          bit.absurd(&2,
            {tri(Bool.cmp(ab, bb), Bool.cmp(bb, cb), LT{}) == True{} : Bool},
            ok)
        case EQ{}:
          bool.tri(ab, bb, cb)
        case GT{}:
          bit.absurd(&2,
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

# LAW: the pair Base carries through a string comparison is not the answer
law rec.snd:
  for +h1: Char
  for +h2: Char
  for r: (String & String) & Cmp
  {String.order.fin(String.cmp.rec(h1, h2, r)) == String.order.fin(r) : Cmp}

def rec.snd(h1, h2, r):
  ((a1, a2), c) = r
  {==}

# LAW: one step of a string comparison, with the char comparison it turns on
# given as a parameter, since a match may not scrutinise a computed value
law order.cons.arm:
  for +h1: Char
  for t1: String
  for +h2: Char
  for t2: String
  for u: Cmp
  {String.order.fin(String.cmp.fin(t1, t2, ((h1, h2), u)))
    == cmp.lex(u, String.order(t1, t2)) : Cmp}

def order.cons.arm(h1, t1, h2, t2, u):
  match u:
    case LT{}:
      {==}
    case EQ{}:
      rec.snd(h1, h2, String.cmp(t1, t2))
    case GT{}:
      {==}

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
      order.cons.arm(Chr{x1}, t1, Chr{x2}, t2, U32.cmp(x1, x2))

# LAW: a lexicographic step taken the other way round flips the answer
law lex.flip:
  for u: Cmp
  for r: Cmp
  {cmp.lex(cmp.flip(u), cmp.flip(r)) == cmp.flip(cmp.lex(u, r)) : Cmp}

def lex.flip(u, r):
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
          bit.absurd(&2, {Cmp.is_lt(r3) == True{} : Bool}, tu)
        case GT{}:
          tu
    case LT{} EQ{}:
      match w:
        case LT{}:
          tri.lt.free(r2)
        case EQ{}:
          bit.absurd(&2, {tri(LT{}, r2, r3) == True{} : Bool}, tu)
        case GT{}:
          bit.absurd(&2, {tri(LT{}, r2, GT{}) == True{} : Bool}, tu)
    case EQ{} LT{}:
      match w:
        case LT{}:
          tri.free.lt(r1)
        case EQ{}:
          bit.absurd(&2, {tri(r1, LT{}, r3) == True{} : Bool}, tu)
        case GT{}:
          bit.absurd(&2, {tri(r1, LT{}, GT{}) == True{} : Bool}, tu)
    case EQ{} EQ{}:
      match w:
        case LT{}:
          bit.absurd(&2, {tri(r1, r2, LT{}) == True{} : Bool}, tu)
        case EQ{}:
          tr
        case GT{}:
          bit.absurd(&2, {tri(r1, r2, GT{}) == True{} : Bool}, tu)
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
    case SNil{} SCon{h2, t2}:
      {==}
    case SCon{h1, t1} SNil{}:
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
    case SNil{} SNil{} SCon{h3, t3}:
      {==}
    case SNil{} SCon{h2, t2} SNil{}:
      {==}
    case SNil{} SCon{h2, t2} SCon{h3, t3}:
      tri.lt.free(String.order(SCon{h2, t2}, SCon{h3, t3}))
    case SCon{h1, t1} SNil{} SNil{}:
      {==}
    case SCon{h1, t1} SNil{} SCon{h3, t3}:
      {==}
    case SCon{h1, t1} SCon{h2, t2} SNil{}:
      tri.mid.gt(String.order(SCon{h1, t1}, SCon{h2, t2}), GT{})
    case SCon{+h1, +t1} SCon{+h2, +t2} SCon{+h3, +t3}:
      str.tri.go(h1, t1, h2, t2, h3, t3, str.tri(t1, t2, t3))

# LAW: a comparison that is at most EQ on two sides is at most EQ across
law le.trans.go:
  for u: Cmp
  for v: Cmp
  for w: Cmp
  for ok: {tri(u, v, w) == True{} : Bool}
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
      bit.absurd(&2, {Cmp.is_le(w) == True{} : Bool}, ev)
    case EQ{} GT{}:
      bit.absurd(&2, {Cmp.is_le(w) == True{} : Bool}, ev)
    case GT{} _:
      bit.absurd(&2, {Cmp.is_le(w) == True{} : Bool}, eu)

# LAW: the order files are written in is transitive, as a total order is
law le.trans:
  for +x: P.File
  for +y: P.File
  for +z: P.File
  for exy: {P.file.le(x, y) == True{} : Bool}
  for eyz: {P.file.le(y, z) == True{} : Bool}
  {P.file.le(x, z) == True{} : Bool}

def le.trans(x, y, z, exy, eyz):
  le.trans.go(
    String.order(P.file.at(x), P.file.at(y)),
    String.order(P.file.at(y), P.file.at(z)),
    String.order(P.file.at(x), P.file.at(z)),
    str.tri(P.file.at(x), P.file.at(y), P.file.at(z)),
    exy, eyz)

# LAW: whether two strings are equal is what their comparison answered
law eq.is.order.go:
  for r: (String & String) & Cmp
  {String.eq.fin(r) == Cmp.is_eq(String.order.fin(r)) : Bool}

def eq.is.order.go(r):
  ((a2, b2), c) = r
  {==}

law eq.is.order:
  for +a: String
  for +b: String
  {String.eq(a, b) == Cmp.is_eq(String.order(a, b)) : Bool}

def eq.is.order(a, b):
  eq.is.order.go(String.cmp(a, b))

# LAW: of two comparisons that are not a tie, exactly one is at most EQ
law le.excl.go:
  for u: Cmp
  for eu: {Cmp.is_eq(u) == False{} : Bool}
  {Cmp.is_le(u) == Bool.not(Cmp.is_le(cmp.flip(u))) : Bool}

def le.excl.go(u, eu):
  match u:
    case LT{}:
      {==}
    case EQ{}:
      bit.absurd2(&2,
        {Cmp.is_le(EQ{}) == Bool.not(Cmp.is_le(cmp.flip(EQ{}))) : Bool}, eu)
    case GT{}:
      {==}

# LAW: two files with different paths sit one way round or the other, never
# both and never neither. This is what the order of a package's files rests
# on: a package holds each path once, so no two of its files tie.
law le.excl:
  for +a: P.File
  for +b: P.File
  for ne: {String.eq(P.file.at(a), P.file.at(b)) == False{} : Bool}
  {P.file.le(a, b) == Bool.not(P.file.le(b, a)) : Bool}

def le.excl(a, b, ne):
  Equal.trans(Bool,
    Cmp.is_le(String.order(P.file.at(a), P.file.at(b))),
    Bool.not(Cmp.is_le(cmp.flip(String.order(P.file.at(a), P.file.at(b))))),
    Bool.not(Cmp.is_le(String.order(P.file.at(b), P.file.at(a)))),
    le.excl.go(String.order(P.file.at(a), P.file.at(b)),
      Equal.trans(Bool,
        Cmp.is_eq(String.order(P.file.at(a), P.file.at(b))),
        String.eq(P.file.at(a), P.file.at(b)),
        False{},
        Equal.sym(Bool, String.eq(P.file.at(a), P.file.at(b)),
          Cmp.is_eq(String.order(P.file.at(a), P.file.at(b))),
          eq.is.order(P.file.at(a), P.file.at(b))),
        ne)),
    Equal.cong(Cmp, Bool, w => Bool.not(Cmp.is_le(w)),
      cmp.flip(String.order(P.file.at(a), P.file.at(b))),
      String.order(P.file.at(b), P.file.at(a)),
      Equal.sym(Cmp, String.order(P.file.at(b), P.file.at(a)),
        cmp.flip(String.order(P.file.at(a), P.file.at(b))),
        str.flip(P.file.at(a), P.file.at(b)))))

# LAW: two files inserted into an empty list in either order land the same way
law ins.swap.nil:
  for +a: P.File
  for +b: P.File
  for ba: Bool
  for eba: {P.file.le(b, a) == ba : Bool}
  for eab: {P.file.le(a, b) == Bool.not(ba) : Bool}
  {P.file.ins(P.file.ins([], a), b) == P.file.ins(P.file.ins([], b), a)
    : List<&2, P.File>}

def ins.swap.nil(a, b, ba, eba, eab):
  match ba:
    case True{}:
      Equal.trans(List<&2, P.File>,
        P.file.ins(P.file.ins([], a), b),
        b <> (a <> []),
        P.file.ins(P.file.ins([], b), a),
        Equal.cong(Bool, List<&2, P.File>,
          y => P.file.ins.put(y, b, a, [], [b]),
          P.file.le(b, a), True{}, eba),
        Equal.sym(List<&2, P.File>,
          P.file.ins(P.file.ins([], b), a), b <> (a <> []),
          Equal.cong(Bool, List<&2, P.File>,
            y => P.file.ins.put(y, a, b, [], [a]),
            P.file.le(a, b), False{}, eab)))
    case False{}:
      Equal.trans(List<&2, P.File>,
        P.file.ins(P.file.ins([], a), b),
        a <> (b <> []),
        P.file.ins(P.file.ins([], b), a),
        Equal.cong(Bool, List<&2, P.File>,
          y => P.file.ins.put(y, b, a, [], [b]),
          P.file.le(b, a), False{}, eba),
        Equal.sym(List<&2, P.File>,
          P.file.ins(P.file.ins([], b), a), a <> (b <> []),
          Equal.cong(Bool, List<&2, P.File>,
            y => P.file.ins.put(y, a, b, [], [a]),
            P.file.le(a, b), True{}, eab)))

# LAW: both files belong before the head, so both end up in front of it, in
# the order their own comparison puts them
law ins.swap.tt:
  for +h: P.File
  for +t: List<&2, P.File>
  for +a: P.File
  for +b: P.File
  for ba: Bool
  for eba: {P.file.le(b, a) == ba : Bool}
  for eab: {P.file.le(a, b) == Bool.not(ba) : Bool}
  for eA: {P.file.le(a, h) == True{} : Bool}
  for eB: {P.file.le(b, h) == True{} : Bool}
  {P.file.ins(P.file.ins.put(True{}, a, h, t, P.file.ins(t, a)), b)
    == P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a)
    : List<&2, P.File>}

def ins.swap.tt(h, t, a, b, ba, eba, eab, eA, eB):
  match ba:
    case True{}:
      Equal.trans(List<&2, P.File>,
        P.file.ins(P.file.ins.put(True{}, a, h, t, P.file.ins(t, a)), b),
        b <> (a <> (h <> t)),
        P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a),
        Equal.trans(List<&2, P.File>,
          P.file.ins(P.file.ins.put(True{}, a, h, t, P.file.ins(t, a)), b),
          P.file.ins.put(P.file.le(b, a), b, a, h <> t, b <> (h <> t)),
          b <> (a <> (h <> t)),
          Equal.cong(List<&2, P.File>, List<&2, P.File>,
            r => P.file.ins.put(P.file.le(b, a), b, a, h <> t, r),
            P.file.ins(h <> t, b), b <> (h <> t),
            Equal.cong(Bool, List<&2, P.File>,
              y => P.file.ins.put(y, b, h, t, P.file.ins(t, b)),
              P.file.le(b, h), True{}, eB)),
          Equal.cong(Bool, List<&2, P.File>,
            y => P.file.ins.put(y, b, a, h <> t, b <> (h <> t)),
            P.file.le(b, a), True{}, eba)),
        Equal.sym(List<&2, P.File>,
          P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a),
          b <> (a <> (h <> t)),
          Equal.trans(List<&2, P.File>,
            P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a),
            P.file.ins.put(P.file.le(a, b), a, b, h <> t, a <> (h <> t)),
            b <> (a <> (h <> t)),
            Equal.cong(List<&2, P.File>, List<&2, P.File>,
              r => P.file.ins.put(P.file.le(a, b), a, b, h <> t, r),
              P.file.ins(h <> t, a), a <> (h <> t),
              Equal.cong(Bool, List<&2, P.File>,
                y => P.file.ins.put(y, a, h, t, P.file.ins(t, a)),
                P.file.le(a, h), True{}, eA)),
            Equal.cong(Bool, List<&2, P.File>,
              y => P.file.ins.put(y, a, b, h <> t, a <> (h <> t)),
              P.file.le(a, b), False{}, eab))))
    case False{}:
      Equal.trans(List<&2, P.File>,
        P.file.ins(P.file.ins.put(True{}, a, h, t, P.file.ins(t, a)), b),
        a <> (b <> (h <> t)),
        P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a),
        Equal.trans(List<&2, P.File>,
          P.file.ins(P.file.ins.put(True{}, a, h, t, P.file.ins(t, a)), b),
          P.file.ins.put(P.file.le(b, a), b, a, h <> t, b <> (h <> t)),
          a <> (b <> (h <> t)),
          Equal.cong(List<&2, P.File>, List<&2, P.File>,
            r => P.file.ins.put(P.file.le(b, a), b, a, h <> t, r),
            P.file.ins(h <> t, b), b <> (h <> t),
            Equal.cong(Bool, List<&2, P.File>,
              y => P.file.ins.put(y, b, h, t, P.file.ins(t, b)),
              P.file.le(b, h), True{}, eB)),
          Equal.cong(Bool, List<&2, P.File>,
            y => P.file.ins.put(y, b, a, h <> t, b <> (h <> t)),
            P.file.le(b, a), False{}, eba)),
        Equal.sym(List<&2, P.File>,
          P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a),
          a <> (b <> (h <> t)),
          Equal.trans(List<&2, P.File>,
            P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a),
            P.file.ins.put(P.file.le(a, b), a, b, h <> t, a <> (h <> t)),
            a <> (b <> (h <> t)),
            Equal.cong(List<&2, P.File>, List<&2, P.File>,
              r => P.file.ins.put(P.file.le(a, b), a, b, h <> t, r),
              P.file.ins(h <> t, a), a <> (h <> t),
              Equal.cong(Bool, List<&2, P.File>,
                y => P.file.ins.put(y, a, h, t, P.file.ins(t, a)),
                P.file.le(a, h), True{}, eA)),
            Equal.cong(Bool, List<&2, P.File>,
              y => P.file.ins.put(y, a, b, h <> t, a <> (h <> t)),
              P.file.le(a, b), True{}, eab))))

# LAW: the first file belongs before the head and the second does not, so the
# second stays behind it and the first goes in front, whichever way round the
# two were offered. A file that came before the first would come before the
# head too, so the branch where one does is no branch at all.
law ins.swap.tf:
  for +h: P.File
  for +t: List<&2, P.File>
  for +a: P.File
  for +b: P.File
  for ba: Bool
  for eba: {P.file.le(b, a) == ba : Bool}
  for eA: {P.file.le(a, h) == True{} : Bool}
  for eB: {P.file.le(b, h) == False{} : Bool}
  {P.file.ins(P.file.ins.put(True{}, a, h, t, P.file.ins(t, a)), b)
    == P.file.ins(P.file.ins.put(False{}, b, h, t, P.file.ins(t, b)), a)
    : List<&2, P.File>}

def ins.swap.tf(h, t, a, b, ba, eba, eA, eB):
  match ba:
    case True{}:
      bit.absurd2(&2,
        {P.file.ins(P.file.ins.put(True{}, a, h, t, P.file.ins(t, a)), b)
          == P.file.ins(P.file.ins.put(False{}, b, h, t, P.file.ins(t, b)), a)
          : List<&2, P.File>},
        Equal.trans(Bool, True{}, P.file.le(b, h), False{},
          Equal.sym(Bool, P.file.le(b, h), True{},
            le.trans(b, a, h, eba, eA)),
          eB))
    case False{}:
      Equal.trans(List<&2, P.File>,
        P.file.ins(P.file.ins.put(True{}, a, h, t, P.file.ins(t, a)), b),
        a <> (h <> P.file.ins(t, b)),
        P.file.ins(P.file.ins.put(False{}, b, h, t, P.file.ins(t, b)), a),
        Equal.trans(List<&2, P.File>,
          P.file.ins(P.file.ins.put(True{}, a, h, t, P.file.ins(t, a)), b),
          P.file.ins.put(P.file.le(b, a), b, a, h <> t, h <> P.file.ins(t, b)),
          a <> (h <> P.file.ins(t, b)),
          Equal.cong(List<&2, P.File>, List<&2, P.File>,
            r => P.file.ins.put(P.file.le(b, a), b, a, h <> t, r),
            P.file.ins(h <> t, b), h <> P.file.ins(t, b),
            Equal.cong(Bool, List<&2, P.File>,
              y => P.file.ins.put(y, b, h, t, P.file.ins(t, b)),
              P.file.le(b, h), False{}, eB)),
          Equal.cong(Bool, List<&2, P.File>,
            y => P.file.ins.put(y, b, a, h <> t, h <> P.file.ins(t, b)),
            P.file.le(b, a), False{}, eba)),
        Equal.sym(List<&2, P.File>,
          P.file.ins(P.file.ins.put(False{}, b, h, t, P.file.ins(t, b)), a),
          a <> (h <> P.file.ins(t, b)),
          Equal.cong(Bool, List<&2, P.File>,
            y => P.file.ins.put(y, a, h, P.file.ins(t, b),
              P.file.ins(P.file.ins(t, b), a)),
            P.file.le(a, h), True{}, eA)))

# LAW: the mirror of the one above, with the two files the other way round
law ins.swap.ft:
  for +h: P.File
  for +t: List<&2, P.File>
  for +a: P.File
  for +b: P.File
  for ab: Bool
  for eab: {P.file.le(a, b) == ab : Bool}
  for eA: {P.file.le(a, h) == False{} : Bool}
  for eB: {P.file.le(b, h) == True{} : Bool}
  {P.file.ins(P.file.ins.put(False{}, a, h, t, P.file.ins(t, a)), b)
    == P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a)
    : List<&2, P.File>}

def ins.swap.ft(h, t, a, b, ab, eab, eA, eB):
  match ab:
    case True{}:
      bit.absurd2(&2,
        {P.file.ins(P.file.ins.put(False{}, a, h, t, P.file.ins(t, a)), b)
          == P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a)
          : List<&2, P.File>},
        Equal.trans(Bool, True{}, P.file.le(a, h), False{},
          Equal.sym(Bool, P.file.le(a, h), True{},
            le.trans(a, b, h, eab, eB)),
          eA))
    case False{}:
      Equal.trans(List<&2, P.File>,
        P.file.ins(P.file.ins.put(False{}, a, h, t, P.file.ins(t, a)), b),
        b <> (h <> P.file.ins(t, a)),
        P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a),
        Equal.cong(Bool, List<&2, P.File>,
          y => P.file.ins.put(y, b, h, P.file.ins(t, a),
            P.file.ins(P.file.ins(t, a), b)),
          P.file.le(b, h), True{}, eB),
        Equal.sym(List<&2, P.File>,
          P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a),
          b <> (h <> P.file.ins(t, a)),
          Equal.trans(List<&2, P.File>,
            P.file.ins(P.file.ins.put(True{}, b, h, t, P.file.ins(t, b)), a),
            P.file.ins.put(P.file.le(a, b), a, b, h <> t,
              h <> P.file.ins(t, a)),
            b <> (h <> P.file.ins(t, a)),
            Equal.cong(List<&2, P.File>, List<&2, P.File>,
              r => P.file.ins.put(P.file.le(a, b), a, b, h <> t, r),
              P.file.ins(h <> t, a), h <> P.file.ins(t, a),
              Equal.cong(Bool, List<&2, P.File>,
                y => P.file.ins.put(y, a, h, t, P.file.ins(t, a)),
                P.file.le(a, h), False{}, eA)),
            Equal.cong(Bool, List<&2, P.File>,
              y => P.file.ins.put(y, a, b, h <> t, h <> P.file.ins(t, a)),
              P.file.le(a, b), False{}, eab))))

# LAW: neither file belongs before the head, so both go past it and the swap
# is the one the shorter list already answered for
law ins.swap.ff:
  for +h: P.File
  for +t: List<&2, P.File>
  for +a: P.File
  for +b: P.File
  for eA: {P.file.le(a, h) == False{} : Bool}
  for eB: {P.file.le(b, h) == False{} : Bool}
  for ih: {P.file.ins(P.file.ins(t, a), b) == P.file.ins(P.file.ins(t, b), a)
    : List<&2, P.File>}
  {P.file.ins(P.file.ins.put(False{}, a, h, t, P.file.ins(t, a)), b)
    == P.file.ins(P.file.ins.put(False{}, b, h, t, P.file.ins(t, b)), a)
    : List<&2, P.File>}

def ins.swap.ff(h, t, a, b, eA, eB, ih):
  Equal.trans(List<&2, P.File>,
    P.file.ins(P.file.ins.put(False{}, a, h, t, P.file.ins(t, a)), b),
    h <> P.file.ins(P.file.ins(t, a), b),
    P.file.ins(P.file.ins.put(False{}, b, h, t, P.file.ins(t, b)), a),
    Equal.cong(Bool, List<&2, P.File>,
      y => P.file.ins.put(y, b, h, P.file.ins(t, a),
        P.file.ins(P.file.ins(t, a), b)),
      P.file.le(b, h), False{}, eB),
    Equal.trans(List<&2, P.File>,
      h <> P.file.ins(P.file.ins(t, a), b),
      h <> P.file.ins(P.file.ins(t, b), a),
      P.file.ins(P.file.ins.put(False{}, b, h, t, P.file.ins(t, b)), a),
      Equal.cong(List<&2, P.File>, List<&2, P.File>, r => h <> r,
        P.file.ins(P.file.ins(t, a), b), P.file.ins(P.file.ins(t, b), a), ih),
      Equal.sym(List<&2, P.File>,
        P.file.ins(P.file.ins.put(False{}, b, h, t, P.file.ins(t, b)), a),
        h <> P.file.ins(P.file.ins(t, b), a),
        Equal.cong(Bool, List<&2, P.File>,
          y => P.file.ins.put(y, a, h, P.file.ins(t, b),
            P.file.ins(P.file.ins(t, b), a)),
          P.file.le(a, h), False{}, eA))))

# LAW: one step of the swap, with the two comparisons against the head given
# as parameters and the equations that put them there given alongside
law ins.swap.arm:
  for +h: P.File
  for +t: List<&2, P.File>
  for +a: P.File
  for +b: P.File
  for A: Bool
  for eA: {P.file.le(a, h) == A : Bool}
  for B: Bool
  for eB: {P.file.le(b, h) == B : Bool}
  for exc: {P.file.le(a, b) == Bool.not(P.file.le(b, a)) : Bool}
  for ih: {P.file.ins(P.file.ins(t, a), b) == P.file.ins(P.file.ins(t, b), a)
    : List<&2, P.File>}
  {P.file.ins(P.file.ins.put(A, a, h, t, P.file.ins(t, a)), b)
    == P.file.ins(P.file.ins.put(B, b, h, t, P.file.ins(t, b)), a)
    : List<&2, P.File>}

def ins.swap.arm(h, t, a, b, A, eA, B, eB, exc, ih):
  match A B:
    case True{} True{}:
      ins.swap.tt(h, t, a, b, P.file.le(b, a), {==}, exc, eA, eB)
    case True{} False{}:
      ins.swap.tf(h, t, a, b, P.file.le(b, a), {==}, eA, eB)
    case False{} True{}:
      ins.swap.ft(h, t, a, b, P.file.le(a, b), {==}, eA, eB)
    case False{} False{}:
      ins.swap.ff(h, t, a, b, eA, eB, ih)

# LAW: two files with different paths inserted into a list in either order
# give the same list. The list is any list: the sort's accumulator is in order
# already, but the induction never needs to say so.
law ins.swap:
  for xs: List<&2, P.File>
  for +a: P.File
  for +b: P.File
  for +ne: {String.eq(P.file.at(a), P.file.at(b)) == False{} : Bool}
  {P.file.ins(P.file.ins(xs, a), b) == P.file.ins(P.file.ins(xs, b), a)
    : List<&2, P.File>}

def ins.swap(xs, a, b, ne):
  match xs:
    case []:
      ins.swap.nil(a, b, P.file.le(b, a), {==}, le.excl(a, b, ne))
    case Con{+h, +t}:
      ins.swap.arm(h, t, a, b, P.file.le(a, h), {==}, P.file.le(b, h), {==},
        le.excl(a, b, ne), ins.swap(t, a, b, ne))

# LAW: the left half of an `and` that answered True
law and.left:
  for u: Bool
  for v: Bool
  for e: {Bool.and(u, v) == True{} : Bool}
  {u == True{} : Bool}

def and.left(u, v, e):
  match u:
    case True{}:
      {==}
    case False{}:
      e

# LAW: the right half of an `and` that answered True
law and.right:
  for u: Bool
  for v: Bool
  for e: {Bool.and(u, v) == True{} : Bool}
  {v == True{} : Bool}

def and.right(u, v, e):
  match u:
    case True{}:
      e
    case False{}:
      bit.absurd(&2, {v == True{} : Bool}, e)

# LAW: what a negation that answered True was told
law not.true:
  for u: Bool
  for e: {Bool.not(u) == True{} : Bool}
  {u == False{} : Bool}

def not.true(u, e):
  match u:
    case True{}:
      bit.absurd(&2, {True{} == False{} : Bool}, e)
    case False{}:
      {==}

# LAW: a path that is none of a list's paths is none of the paths of that
# list with one more file put in it, as long as it is not that file's either
law fresh.ins_at:
  for +n: Nat
  for +x: P.File
  for +y: P.File
  for +xs: List<&2, P.File>
  for nxy: {String.eq(P.file.at(x), P.file.at(y)) == False{} : Bool}
  for +fx: {Laws.fresh(x, xs) == True{} : Bool}
  {Laws.fresh(x, Laws.perm.ins_at(n, y, xs)) == True{} : Bool}

def fresh.ins_at(n, x, y, xs, nxy, fx):
  match n xs:
    case 0n _:
      Equal.trans(Bool,
        Laws.fresh(x, y <> xs),
        Laws.fresh(x, xs),
        True{},
        Equal.cong(Bool, Bool,
          u => Bool.and(Bool.not(u), Laws.fresh(x, xs)),
          String.eq(P.file.at(x), P.file.at(y)), False{}, nxy),
        fx)
    case 1n+p Nil{}:
      Equal.cong(Bool, Bool, u => Bool.and(Bool.not(u), True{}),
        String.eq(P.file.at(x), P.file.at(y)), False{}, nxy)
    case 1n+p Con{+h, +t}:
      Equal.trans(Bool,
        Laws.fresh(x, h <> Laws.perm.ins_at(p, y, t)),
        Bool.and(Bool.not(String.eq(P.file.at(x), P.file.at(h))), True{}),
        True{},
        Equal.cong(Bool, Bool,
          v => Bool.and(Bool.not(String.eq(P.file.at(x), P.file.at(h))), v),
          Laws.fresh(x, Laws.perm.ins_at(p, y, t)), True{},
          fresh.ins_at(p, x, y, t, nxy,
            and.right(Bool.not(String.eq(P.file.at(x), P.file.at(h))),
              Laws.fresh(x, t), fx))),
        Equal.cong(Bool, Bool, u => Bool.and(u, True{}),
          Bool.not(String.eq(P.file.at(x), P.file.at(h))), True{},
          and.left(Bool.not(String.eq(P.file.at(x), P.file.at(h))),
            Laws.fresh(x, t), fx)))

# LAW: rearranging a list does not put a path in it that was not there
law fresh.perm:
  for +x: P.File
  for +ns: List<&2, Nat>
  for +xs: List<&2, P.File>
  for +fx: {Laws.fresh(x, xs) == True{} : Bool}
  {Laws.fresh(x, Laws.perm(ns, xs)) == True{} : Bool}

def fresh.perm(x, ns, xs, fx):
  match ns xs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{h, t}:
      fx
    case Con{n, ms} Nil{}:
      {==}
    case Con{+n, +ms} Con{+h, +t}:
      fresh.ins_at(n, x, h, Laws.perm(ms, t),
        not.true(String.eq(P.file.at(x), P.file.at(h)),
          and.left(Bool.not(String.eq(P.file.at(x), P.file.at(h))),
            Laws.fresh(x, t), fx)),
        fresh.perm(x, ms, t,
          and.right(Bool.not(String.eq(P.file.at(x), P.file.at(h))),
            Laws.fresh(x, t), fx)))

# LAW: sorting a list with one more file put anywhere in it is sorting the
# list and inserting that file. Where the file was put makes no difference,
# which is the whole of the order-independence, said one file at a time.
law sort.ins_at:
  for +n: Nat
  for +x: P.File
  for +xs: List<&2, P.File>
  for +fr: {Laws.fresh(x, xs) == True{} : Bool}
  {P.file.sort(Laws.perm.ins_at(n, x, xs)) == P.file.ins(P.file.sort(xs), x)
    : List<&2, P.File>}

def sort.ins_at(n, x, xs, fr):
  match n xs:
    case 0n _:
      {==}
    case 1n+p Nil{}:
      {==}
    case 1n+p Con{+h, +t}:
      Equal.trans(List<&2, P.File>,
        P.file.sort(h <> Laws.perm.ins_at(p, x, t)),
        P.file.ins(P.file.ins(P.file.sort(t), x), h),
        P.file.ins(P.file.ins(P.file.sort(t), h), x),
        Equal.cong(List<&2, P.File>, List<&2, P.File>,
          r => P.file.ins(r, h),
          P.file.sort(Laws.perm.ins_at(p, x, t)),
          P.file.ins(P.file.sort(t), x),
          sort.ins_at(p, x, t,
            and.right(Bool.not(String.eq(P.file.at(x), P.file.at(h))),
              Laws.fresh(x, t), fr))),
        ins.swap(P.file.sort(t), x, h,
          not.true(String.eq(P.file.at(x), P.file.at(h)),
            and.left(Bool.not(String.eq(P.file.at(x), P.file.at(h))),
              Laws.fresh(x, t), fr))))

def Laws.sort_perm(ns, xs, dis):
  match ns xs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{h, t}:
      {==}
    case Con{n, ms} Nil{}:
      {==}
    case Con{+n, +ms} Con{+h, +t}:
      Equal.trans(List<&2, P.File>,
        P.file.sort(Laws.perm.ins_at(n, h, Laws.perm(ms, t))),
        P.file.ins(P.file.sort(Laws.perm(ms, t)), h),
        P.file.ins(P.file.sort(t), h),
        sort.ins_at(n, h, Laws.perm(ms, t),
          fresh.perm(h, ms, t,
            and.left(Laws.fresh(h, t), Laws.distinct(t), dis))),
        Equal.cong(List<&2, P.File>, List<&2, P.File>,
          r => P.file.ins(r, h),
          P.file.sort(Laws.perm(ms, t)), P.file.sort(t),
          Laws.sort_perm(ms, t,
            and.right(Laws.fresh(h, t), Laws.distinct(t), dis))))

def Laws.manifest_perm(ns, xs, dis):
  Equal.cong(List<&2, P.File>, String,
    ys => P.manifest.lines(P.dedup(ys)),
    P.file.sort(Laws.perm(ns, xs)), P.file.sort(xs),
    Laws.sort_perm(ns, xs, dis))

def Laws.hash_perm(ns, xs, dis):
  Equal.cong(String, String,
    m => "0x" ++ String.take(Sha.hex(m), 32n),
    P.manifest_of(Laws.perm(ns, xs)), P.manifest_of(xs),
    Laws.manifest_perm(ns, xs, dis))

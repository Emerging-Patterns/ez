# check/str: the string facts a proof needs and Base does not state. A string
# is a list of chars, and the readers in this repo walk it as one, cut it at a
# separator and join the pieces back, and compare it char by char. Every law
# here is stated for all strings, so a proof about a reader or a writer can
# lean on it for the text it is about. They were first proved in the lock
# planner spike (docs/rfc/ez-lock-planner.md); they belong here, beside
# check/eq.bend, so every proof can use them. check/PROOF.bend puts them
# through the gate whether or not a proof uses them yet.
import Base
import ./eq.bend as Eq

# Strings as lists of chars.

# LAW: a string's chars joined are the chars of the two joined
law to_list_append:
  for +a: String
  for +b: String
  {String.to_list(String.append(a, b))
    == List.append(&2, Char, String.to_list(a), String.to_list(b))
    : List<&2, Char>}

# by induction on the first string, one char at a time
def to_list_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(List<&2, Char>, List<&2, Char>, cs => h <> cs,
        String.to_list(String.append(t, b)),
        List.append(&2, Char, String.to_list(t), String.to_list(b)),
        to_list_append(t, b))

# LAW: chars appended to a string's chars read back as the string and then
# them
law from_to_append:
  for +v: String
  for +ys: List<&2, Char>
  {String.from_list(List.append(&2, Char, String.to_list(v), ys))
    == String.append(v, String.from_list(ys)) : String}

# and the same for reading them back
def from_to_append(v, ys):
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, s => SCon{h, s},
        String.from_list(List.append(&2, Char, String.to_list(t), ys)),
        String.append(t, String.from_list(ys)),
        from_to_append(t, ys))

# LAW: a string's chars read back as the string
law from_to:
  for +v: String
  {String.from_list(String.to_list(v)) == v : String}

# by induction on the string
def from_to(v):
  match v:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, s => SCon{h, s},
        String.from_list(String.to_list(t)), t, from_to(t))

# Reversal. Base reverses a list onto an accumulator, and a reader that trims
# both ends of a line reverses it twice.

# LAW: reversing onto an accumulator goes through an append one half at a time
law rev_append:
  for +xs: List<&2, Char>
  for +ys: List<&2, Char>
  for +acc: List<&2, Char>
  {List.reverse.go(&2, Char, List.append(&2, Char, xs, ys), acc)
    == List.reverse.go(&2, Char, ys, List.reverse.go(&2, Char, xs, acc))
    : List<&2, Char>}

# by induction on the first half: its chars go onto the accumulator
def rev_append(xs, ys, acc):
  match xs:
    case []:
      {==}
    case +h <> +t:
      rev_append(t, ys, h <> acc)

# LAW: reversing twice puts the first list back in front of the second
# accumulator
law rev_rev:
  for +xs: List<&2, Char>
  for +ys: List<&2, Char>
  for +zs: List<&2, Char>
  {List.reverse.go(&2, Char, List.reverse.go(&2, Char, xs, ys), zs)
    == List.reverse.go(&2, Char, ys, List.append(&2, Char, xs, zs))
    : List<&2, Char>}

# by induction on the first list: each char goes over and back
def rev_rev(xs, ys, zs):
  match xs:
    case []:
      {==}
    case +h <> +t:
      rev_rev(t, h <> ys, zs)

# Equality. Base compares a char as a 32-bit word and a string char by char,
# and states no fact that a comparison which answered equal was given one
# thing twice. Two words that compare equal are one word by induction on the
# width, and two strings by induction on the string.

# the type that is empty exactly where a comparison answered EQ
def cmp.emp(ans: Cmp) -> Type:
  match ans:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Unit

def cmp.lt(eq: {LT{} == EQ{} : Cmp}) -> Empty:
  %eq : cmp.emp(_)
  Unit{}

def cmp.gt(eq: {GT{} == EQ{} : Cmp}) -> Empty:
  %eq : cmp.emp(_)
  Unit{}

# LAW: a comparison that reads as equal is EQ
law cmp_is_eq:
  for c: Cmp
  for e: {Cmp.is_eq(c) == True{} : Bool}
  {c == EQ{} : Cmp}

# the two other answers read as False
def cmp_is_eq(c, e):
  match c:
    case LT{}:
      Eq.bit.absurd(&2, {LT{} == EQ{} : Cmp}, e)
    case EQ{}:
      {==}
    case GT{}:
      Eq.bit.absurd(&2, {GT{} == EQ{} : Cmp}, e)

# LAW: two bits that compare equal are one bit
law bool_eq:
  for a: Bool
  for b: Bool
  for e: {Bool.cmp(a, b) == EQ{} : Cmp}
  {a == b : Bool}

# the two bits that differ compare LT or GT
def bool_eq(a, b, e):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      Eq.bit.gone(&2, {False{} == True{} : Bool}, cmp.lt(e))
    case True{} False{}:
      Eq.bit.gone(&2, {True{} == False{} : Bool}, cmp.gt(e))
    case True{} True{}:
      {==}

# LAW: a word comparison that ends EQ had tails that compared EQ
law fin_tail:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {t == EQ{} : Cmp}

# an answer of LT or GT from the tails is the answer, never EQ
def fin_tail(_ab, _bb, t, e):
  match t:
    case LT{}:
      Eq.bit.gone(&2, {LT{} == EQ{} : Cmp}, cmp.lt(e))
    case EQ{}:
      {==}
    case GT{}:
      Eq.bit.gone(&2, {GT{} == EQ{} : Cmp}, cmp.gt(e))

# LAW: and heads that compared EQ
law fin_head:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  for e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp}
  {Bool.cmp(ab, bb) == EQ{} : Cmp}

# and an EQ from the tails leaves the heads to answer
def fin_head(ab, bb, t, e):
  match t:
    case LT{}:
      Eq.bit.gone(&2, {Bool.cmp(ab, bb) == EQ{} : Cmp}, cmp.lt(e))
    case EQ{}:
      e
    case GT{}:
      Eq.bit.gone(&2, {Bool.cmp(ab, bb) == EQ{} : Cmp}, cmp.gt(e))

# LAW: two words that compare equal are one word
law word_eq:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  for +e: {Word.cmp(n, a, b) == EQ{} : Cmp}
  {a == b : Word(n)}

# by induction on the width: the heads by the bit law, then the tails
def word_eq(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          Equal.trans(Word(1n+p), WCon{ab, at}, WCon{bb, at}, WCon{bb, bt},
            Equal.cong(Bool, Word(1n+p), x => WCon{x, at}, ab, bb,
              bool_eq(ab, bb, fin_head(ab, bb, Word.cmp(p, at, bt), e))),
            Equal.cong(Word(p), Word(1n+p), y => WCon{bb, y}, at, bt,
              word_eq(p, at, bt, fin_tail(ab, bb, Word.cmp(p, at, bt), e))))

# LAW: two code points that compare equal are one char
law u32_eq:
  for x: U32
  for y: U32
  for e: {U32.is_eq(x, y) == True{} : Bool}
  {Chr{x} == Chr{y} : Char}

# a code point is a word of thirty-two bits
def u32_eq(x, y, e):
  match x y:
    case U32{+wx} U32{+wy}:
      Equal.cong(Word(32n), Char, w => Chr{U32{w}}, wx, wy,
        word_eq(32n, wx, wy, cmp_is_eq(Word.cmp(32n, wx, wy), e)))

# LAW: two chars that compare equal are one char
law char_eq_true:
  for a: Char
  for b: Char
  for e: {Char.is_eq(a, b) == True{} : Bool}
  {a == b : Char}

# a char is a code point
def char_eq_true(a, b, e):
  match a b:
    case Chr{x} Chr{y}:
      u32_eq(x, y, e)

# LAW: a string comparison read as a bit reads only the comparison, so the
# chars it rebuilt in front do not change it
law eq_fin_rec:
  for h1: Char
  for h2: Char
  for r: (String & String) & Cmp
  {String.eq.fin(String.cmp.rec(h1, h2, r)) == String.eq.fin(r) : Bool}

# the comparison, taken apart and put back together
def eq_fin_rec(_h1, _h2, r):
  match r:
    case (ts, c):
      match ts:
        case (t1, t2):
          {==}

# LAW: two strings that read as equal, whose heads compared as the given
# answer, have one head. The answer is a parameter so that the arms it did not
# take can be closed.
law eq_head.cmp:
  for +x: U32
  for +y: U32
  for t1: String
  for t2: String
  for c: Cmp
  for ec: {U32.cmp(x, y) == c : Cmp}
  for e: {String.eq.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c)))
    == True{} : Bool}
  {Chr{x} == Chr{y} : Char}

def eq_head.cmp(x, y, _t1, _t2, c, ec, e):
  match c:
    case LT{}:
      Eq.bit.absurd(&2, {Chr{x} == Chr{y} : Char}, e)
    case EQ{}:
      u32_eq(x, y, Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), U32.cmp(x, y),
        EQ{}, ec))
    case GT{}:
      Eq.bit.absurd(&2, {Chr{x} == Chr{y} : Char}, e)

# LAW: and tails that read as equal
law eq_tail.cmp:
  for x: U32
  for y: U32
  for +t1: String
  for +t2: String
  for c: Cmp
  for ec: {U32.cmp(x, y) == c : Cmp}
  for e: {String.eq.fin(String.cmp.fin(t1, t2, ((Chr{x}, Chr{y}), c)))
    == True{} : Bool}
  {String.eq(t1, t2) == True{} : Bool}

def eq_tail.cmp(x, y, t1, t2, c, _ec, e):
  match c:
    case LT{}:
      Eq.bit.absurd(&2, {String.eq(t1, t2) == True{} : Bool}, e)
    case EQ{}:
      Equal.trans(Bool,
        String.eq(t1, t2),
        String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
        True{},
        Equal.sym(Bool,
          String.eq.fin(String.cmp.rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
          String.eq(t1, t2),
          eq_fin_rec(Chr{x}, Chr{y}, String.cmp(t1, t2))),
        e)
    case GT{}:
      Eq.bit.absurd(&2, {String.eq(t1, t2) == True{} : Bool}, e)

# LAW: two strings with a first char each, which read as equal, have one
# first char
law eq_head:
  for h1: Char
  for h2: Char
  for +t1: String
  for +t2: String
  for e: {String.eq(SCon{h1, t1}, SCon{h2, t2}) == True{} : Bool}
  {h1 == h2 : Char}

# the heads' comparison is the answer the first arm is given
def eq_head(h1, h2, t1, t2, e):
  match h1 h2:
    case Chr{+x} Chr{+y}:
      eq_head.cmp(x, y, t1, t2, U32.cmp(x, y), {==}, e)

# LAW: and the rest of each reads as equal
law eq_tail:
  for h1: Char
  for h2: Char
  for +t1: String
  for +t2: String
  for e: {String.eq(SCon{h1, t1}, SCon{h2, t2}) == True{} : Bool}
  {String.eq(t1, t2) == True{} : Bool}

# and the answer the second arm is given
def eq_tail(h1, h2, t1, t2, e):
  match h1 h2:
    case Chr{+x} Chr{+y}:
      eq_tail.cmp(x, y, t1, t2, U32.cmp(x, y), {==}, e)

# LAW: two strings that compare equal are one string
law string_eq_true:
  for a: String
  for b: String
  for +e: {String.eq(a, b) == True{} : Bool}
  {a == b : String}

# by induction on both strings: two of different lengths never read as
# equal, and two with a first char each have one head and equal tails
def string_eq_true(a, b, e):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{h, t}:
      Eq.bit.absurd(&2, {SNil{} == SCon{h, t} : String}, e)
    case SCon{h, t} SNil{}:
      Eq.bit.absurd(&2, {SCon{h, t} == SNil{} : String}, e)
    case SCon{+h1, +t1} SCon{+h2, +t2}:
      Equal.trans(String, SCon{h1, t1}, SCon{h2, t1}, SCon{h2, t2},
        Equal.cong(Char, String, h => SCon{h, t1}, h1, h2,
          eq_head(h1, h2, t1, t2, e)),
        Equal.cong(String, String, t => SCon{h2, t}, t1, t2,
          string_eq_true(t1, t2, eq_tail(h1, h2, t1, t2, e))))

# Cutting and joining. The readers cut a line at a separator and join the
# pieces back with it; the writers join pieces that hold no separator, which
# the reader cuts back into the same pieces.

# LAW: one step of a split always leaves at least one piece
law fin_cons:
  for h: Char
  for r: List<&2, String>
  for b: Bool
  {List.is_empty(&2, String, String.split.fin(h, r, b)) == False{} : Bool}

# LAW: a char pushed onto the pieces leaves at least one
law push_cons:
  for h: Char
  for r: List<&2, String>
  {List.is_empty(&2, String, String.split.push(h, r)) == False{} : Bool}

# a push onto no pieces makes one, and onto some keeps them
def push_cons(_h, r):
  match r:
    case []:
      {==}
    case y <> ys:
      {==}

# a cut adds a piece, and a push leaves one
def fin_cons(h, r, b):
  match b:
    case False{}:
      push_cons(h, r)
    case True{}:
      {==}

# LAW: and so does a whole split
law split_cons:
  for s: String
  for +c: Char
  {List.is_empty(&2, String, String.split(s, c)) == False{} : Bool}

# the empty string is one empty piece, and a longer one is a step
def split_cons(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      fin_cons(h, String.split(t, c), Char.is_eq(h, c))

# LAW: a join that starts from a piece with a char in front has the char in
# front
law join_go_cons:
  for ys: List<&2, String>
  for y: String
  for h: Char
  for +sep: String
  {String.join.go(ys, SCon{h, y}, sep) == SCon{h, String.join.go(ys, y, sep)}
    : String}

# the first piece is appended first, char by char
def join_go_cons(ys, _y, _h, _sep):
  match ys:
    case []:
      {==}
    case y2 <> t:
      {==}

# LAW: one char of the split joined back, once the rest is known to have a
# first piece, with which way the comparison went given as a parameter
law join_split.cons:
  for +h: Char
  for +t: String
  for +c: Char
  for +y: String
  for +ys: List<&2, String>
  for b: Bool
  for eb: {Char.is_eq(h, c) == b : Bool}
  for ih: {String.join.go(ys, y, SCon{c, SNil{}}) == t : String}
  {String.join(String.split.fin(h, y <> ys, b), SCon{c, SNil{}}) == SCon{h, t}
    : String}

def join_split.cons(h, t, c, y, ys, b, eb, ih):
  match b:
    case False{}:
      Equal.trans(String,
        String.join.go(ys, SCon{h, y}, SCon{c, SNil{}}),
        SCon{h, String.join.go(ys, y, SCon{c, SNil{}})},
        SCon{h, t},
        join_go_cons(ys, y, h, SCon{c, SNil{}}),
        Equal.cong(String, String, x => SCon{h, x},
          String.join.go(ys, y, SCon{c, SNil{}}), t, ih))
    case True{}:
      Equal.trans(String,
        SCon{c, String.join.go(ys, y, SCon{c, SNil{}})},
        SCon{c, t},
        SCon{h, t},
        Equal.cong(String, String, x => SCon{c, x},
          String.join.go(ys, y, SCon{c, SNil{}}), t, ih),
        Equal.cong(Char, String, x => SCon{x, t}, c, h,
          Equal.sym(Char, h, c, char_eq_true(h, c, eb))))

# LAW: one char of the split, joined back, with which way the comparison went
# and the pieces of the rest given as parameters
law join_split.arm:
  for +h: Char
  for +t: String
  for +c: Char
  for r: List<&2, String>
  for b: Bool
  for eb: {Char.is_eq(h, c) == b : Bool}
  for er: {List.is_empty(&2, String, r) == False{} : Bool}
  for ih: {String.join(r, SCon{c, SNil{}}) == t : String}
  {String.join(String.split.fin(h, r, b), SCon{c, SNil{}}) == SCon{h, t}
    : String}

def join_split.arm(h, t, c, r, b, eb, er, ih):
  match r:
    case []:
      Eq.bit.absurd2(&2, {String.join(String.split.fin(h, [], b),
        SCon{c, SNil{}}) == SCon{h, t} : String}, er)
    case +y <> +ys:
      join_split.cons(h, t, c, y, ys, b, eb, ih)

# LAW: cutting a string at a char and joining the pieces back with it gives
# the string back, whatever it holds
law join_split:
  for s: String
  for +c: Char
  {String.join(String.split(s, c), SCon{c, SNil{}}) == s : String}

# by induction on the string, each char with its own arm
def join_split(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      join_split.arm(h, t, c, String.split(t, c), Char.is_eq(h, c), {==},
        split_cons(t, c), join_split(t, c))

# whether a string holds no copy of a char. Law vocabulary: ez never calls it.
def clear(text: String, +sep: Char) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{h, t}:
      rest = clear(t, sep)
      Bool.and(Bool.not(Char.is_eq(h, sep)), rest)

# whether no string of a list holds a copy of a char
def clear.all(ps: List<&2, String>, +sep: Char) -> Bool:
  match ps:
    case []:
      True{}
    case h <> t:
      rest = clear.all(t, sep)
      Bool.and(clear(h, sep), rest)

# LAW: a string with nothing after it is the string
law append_nil:
  for +s: String
  {String.append(s, SNil{}) == s : String}

# by induction on the string
def append_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(t, SNil{}), t,
        append_nil(t))

# LAW: a string that holds no separator, put in front of text, lands whole in
# front of the text's first piece
law split_front:
  for p: String
  for +s: String
  for +c: Char
  for +y: String
  for +ys: List<&2, String>
  for +ep: {clear(p, c) == True{} : Bool}
  for es: {String.split(s, c) == y <> ys : List<&2, String>}
  {String.split(String.append(p, s), c) == String.append(p, y) <> ys
    : List<&2, String>}

# by induction on the string in front: each char is no separator, so it
# is pushed onto the first piece
def split_front(p, s, c, y, ys, ep, es):
  match p:
    case SNil{}:
      es
    case SCon{+h, +t}:
      Equal.trans(List<&2, String>,
        String.split.fin(h, String.split(String.append(t, s), c),
          Char.is_eq(h, c)),
        String.split.push(h, String.split(String.append(t, s), c)),
        SCon{h, String.append(t, y)} <> ys,
        Equal.cong(Bool, List<&2, String>,
          b => String.split.fin(h, String.split(String.append(t, s), c), b),
          Char.is_eq(h, c), False{},
          Eq.not.true(Char.is_eq(h, c),
            Eq.and.left(Bool.not(Char.is_eq(h, c)), clear(t, c), ep))),
        Equal.cong(List<&2, String>, List<&2, String>,
          r => String.split.push(h, r),
          String.split(String.append(t, s), c),
          String.append(t, y) <> ys,
          split_front(t, s, c, y, ys,
            Eq.and.right(Bool.not(Char.is_eq(h, c)), clear(t, c), ep), es)))

# LAW: a string that holds no separator is one piece
law split_one:
  for +p: String
  for +c: Char
  for ep: {clear(p, c) == True{} : Bool}
  {String.split(p, c) == [p] : List<&2, String>}

# the string with an empty text after it, whose one piece is empty
def split_one(p, c, ep):
  Equal.trans(List<&2, String>,
    String.split(p, c),
    String.split(String.append(p, SNil{}), c),
    [p],
    Equal.cong(String, List<&2, String>, s => String.split(s, c),
      p, String.append(p, SNil{}), Equal.sym(String,
        String.append(p, SNil{}), p, append_nil(p))),
    Equal.trans(List<&2, String>,
      String.split(String.append(p, SNil{}), c),
      [String.append(p, SNil{})],
      [p],
      split_front(p, SNil{}, c, SNil{}, [], ep, {==}),
      Equal.cong(String, List<&2, String>, s => [s],
        String.append(p, SNil{}), p, append_nil(p))))

# LAW: the separator in front of text is an empty piece in front of the
# text's pieces
law split_sep:
  for +c: Char
  for +s: String
  {String.split(SCon{c, s}, c) == SNil{} <> String.split(s, c)
    : List<&2, String>}

# the separator compares equal to itself, so it cuts
def split_sep(c, s):
  Equal.cong(Bool, List<&2, String>,
    b => String.split.fin(c, String.split(s, c), b),
    Char.is_eq(c, c), True{}, Eq.char_eq_self(c))

# LAW: pieces joined from a first piece, cut back, when none holds the
# separator
law split_join.go:
  for +ps: List<&2, String>
  for +p: String
  for +c: Char
  for ep: {clear(p, c) == True{} : Bool}
  for +eps: {clear.all(ps, c) == True{} : Bool}
  {String.split(String.join.go(ps, p, SCon{c, SNil{}}), c) == p <> ps
    : List<&2, String>}

def split_join.go(ps, p, c, ep, eps):
  match ps:
    case []:
      split_one(p, c, ep)
    case +q <> +qs:
      Equal.trans(List<&2, String>,
        String.split(String.append(p,
          SCon{c, String.join.go(qs, q, SCon{c, SNil{}})}), c),
        String.append(p, SNil{}) <> q <> qs,
        p <> q <> qs,
        split_front(p, SCon{c, String.join.go(qs, q, SCon{c, SNil{}})}, c,
          SNil{}, q <> qs, ep,
          Equal.trans(List<&2, String>,
            String.split(SCon{c, String.join.go(qs, q, SCon{c, SNil{}})}, c),
            SNil{} <> String.split(String.join.go(qs, q, SCon{c, SNil{}}), c),
            SNil{} <> q <> qs,
            split_sep(c, String.join.go(qs, q, SCon{c, SNil{}})),
            Equal.cong(List<&2, String>, List<&2, String>, r => SNil{} <> r,
              String.split(String.join.go(qs, q, SCon{c, SNil{}}), c),
              q <> qs,
              split_join.go(qs, q, c,
                Eq.and.left(clear(q, c), clear.all(qs, c), eps),
                Eq.and.right(clear(q, c), clear.all(qs, c), eps))))),
        Equal.cong(String, List<&2, String>, x => x <> q <> qs,
          String.append(p, SNil{}), p, append_nil(p)))

# LAW: joining pieces with a separator none of them holds, and cutting the
# text at it, gives the pieces back. A list with no pieces joins to the empty
# text, which is one empty piece, so the law is about a list with a first one.
law split_join:
  for +p: String
  for +ps: List<&2, String>
  for +c: Char
  for +e: {clear.all(p <> ps, c) == True{} : Bool}
  {String.split(String.join(p <> ps, SCon{c, SNil{}}), c) == p <> ps
    : List<&2, String>}

# the join starts from the first piece, and the list's hypothesis is
# the first piece's and the rest's
def split_join(p, ps, c, e):
  split_join.go(ps, p, c, Eq.and.left(clear(p, c), clear.all(ps, c), e),
    Eq.and.right(clear(p, c), clear.all(ps, c), e))

# Orders, lists of any data, and more string facts, for the lock's proofs
# (lock/PROOF.bend); none is about the lock.

# the type that is empty exactly where a comparison answered LT
def cmp.lt_emp(ans: Cmp) -> Type:
  match ans:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Unit

def cmp.eq_lt(eq: {EQ{} == LT{} : Cmp}) -> Empty:
  %eq : cmp.lt_emp(_)
  Unit{}

def cmp.gt_lt(eq: {GT{} == LT{} : Cmp}) -> Empty:
  %eq : cmp.lt_emp(_)
  Unit{}

# LAW: a word at or below a second, which is below a third, is below the
# third
law word_le_lt:
  for +n: Nat
  for x: Word(n)
  for a: Word(n)
  for b: Word(n)
  for exa: {Cmp.is_gt(Word.cmp(n, x, a)) == False{} : Bool}
  for eab: {Word.cmp(n, a, b) == LT{} : Cmp}
  {Word.cmp(n, x, b) == LT{} : Cmp}

# the step, with the tails' two answers given, so the arms they rule out
# can be closed
law wlt_step:
  for +p: Nat
  for +xb: Bool
  for +ab: Bool
  for +bb: Bool
  for +xt: Word(p)
  for +at: Word(p)
  for +bt: Word(p)
  for r1: Cmp
  for e1: {Word.cmp(p, xt, at) == r1 : Cmp}
  for r2: Cmp
  for e2: {Word.cmp(p, at, bt) == r2 : Cmp}
  for exa: {Cmp.is_gt(Word.cmp.fin(xb, ab, r1)) == False{} : Bool}
  for eab: {Word.cmp.fin(ab, bb, r2) == LT{} : Cmp}
  for ih: {Cmp.is_gt(Word.cmp(p, xt, at)) == False{} : Bool}
    -> {Word.cmp(p, at, bt) == LT{} : Cmp} -> {Word.cmp(p, xt, bt) == LT{} : Cmp}
  {Word.cmp.fin(xb, bb, Word.cmp(p, xt, bt)) == LT{} : Cmp}

# the heads, when the tails are one word: the second head is below the third,
# so it is False and the third True, and the first is not above False
law bits_le_lt:
  for xb: Bool
  for ab: Bool
  for bb: Bool
  for exa: {Cmp.is_gt(Bool.cmp(xb, ab)) == False{} : Bool}
  for eab: {Bool.cmp(ab, bb) == LT{} : Cmp}
  {Bool.cmp(xb, bb) == LT{} : Cmp}

# the four ways two bits compare, each closed by the premises
def bits_le_lt(xb, ab, bb, exa, eab):
  match xb ab bb:
    case False{} False{} True{}:
      {==}
    case True{} False{} True{}:
      Eq.bit.absurd2(&2, {EQ{} == LT{} : Cmp}, exa)
    case _ False{} False{}:
      Eq.bit.gone(&2, {Bool.cmp(xb, False{}) == LT{} : Cmp}, cmp.eq_lt(eab))
    case _ True{} False{}:
      Eq.bit.gone(&2, {Bool.cmp(xb, False{}) == LT{} : Cmp}, cmp.gt_lt(eab))
    case _ True{} True{}:
      Eq.bit.gone(&2, {Bool.cmp(xb, True{}) == LT{} : Cmp}, cmp.eq_lt(eab))

# the tails' answers decide it, and when they are EQ the heads do
def wlt_step(p, xb, ab, bb, xt, at, bt, r1, e1, r2, e2, exa, eab, ih):
  match r1 r2:
    case LT{} LT{}:
      Equal.cong(Cmp, Cmp, c => Word.cmp.fin(xb, bb, c),
        Word.cmp(p, xt, bt), LT{},
        ih(
          Equal.cong(Cmp, Bool, c => Cmp.is_gt(c), Word.cmp(p, xt, at), LT{}, e1),
          e2))
    case EQ{} LT{}:
      Equal.cong(Cmp, Cmp, c => Word.cmp.fin(xb, bb, c),
        Word.cmp(p, xt, bt), LT{},
        Equal.trans(Cmp, Word.cmp(p, xt, bt), Word.cmp(p, at, bt), LT{},
          Equal.cong(Word(p), Cmp, w => Word.cmp(p, w, bt), xt, at,
            word_eq(p, xt, at, e1)),
          e2))
    case LT{} EQ{}:
      Equal.cong(Cmp, Cmp, c => Word.cmp.fin(xb, bb, c),
        Word.cmp(p, xt, bt), LT{},
        Equal.trans(Cmp, Word.cmp(p, xt, bt), Word.cmp(p, xt, at), LT{},
          Equal.cong(Word(p), Cmp, w => Word.cmp(p, xt, w), bt, at,
            Equal.sym(Word(p), at, bt, word_eq(p, at, bt, e2))),
          e1))
    case EQ{} EQ{}:
      Equal.trans(Cmp,
        Word.cmp.fin(xb, bb, Word.cmp(p, xt, bt)),
        Word.cmp.fin(xb, bb, EQ{}),
        LT{},
        Equal.cong(Cmp, Cmp, c => Word.cmp.fin(xb, bb, c),
          Word.cmp(p, xt, bt), EQ{},
          Equal.trans(Cmp, Word.cmp(p, xt, bt), Word.cmp(p, at, bt), EQ{},
            Equal.cong(Word(p), Cmp, w => Word.cmp(p, w, bt), xt, at,
              word_eq(p, xt, at, e1)),
            e2)),
        bits_le_lt(xb, ab, bb, exa, eab))
    case GT{} _:
      Eq.bit.absurd2(&2, {Word.cmp.fin(xb, bb, Word.cmp(p, xt, bt)) == LT{} : Cmp}, exa)
    case _ GT{}:
      Eq.bit.gone(&2, {Word.cmp.fin(xb, bb, Word.cmp(p, xt, bt)) == LT{} : Cmp},
        cmp.gt_lt(eab))

# by induction on the width, with the tails' law handed to the step
def word_le_lt(n, x, a, b, exa, eab):
  match n:
    case 0n:
      match x a b:
        case WNil{} WNil{} WNil{}:
          Eq.bit.gone(&2, {EQ{} == LT{} : Cmp}, cmp.eq_lt(eab))
    case 1n+p:
      match x a b:
        case WCon{+xb, +xt} WCon{+ab, +at} WCon{+bb, +bt}:
          wlt_step(p, xb, ab, bb, xt, at, bt,
            Word.cmp(p, xt, at), {==}, Word.cmp(p, at, bt), {==}, exa, eab,
            h1 => h2 => word_le_lt(p, xt, at, bt, h1, h2))

# LAW: an `and` whose right half is False is False
law and_false:
  for a: Bool
  {Bool.and(a, False{}) == False{} : Bool}

# both values of the left half
def and_false(a):
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# LAW: an `and` of two halves that answered True
law and_true:
  for u: Bool
  for v: Bool
  for eu: {u == True{} : Bool}
  for ev: {v == True{} : Bool}
  {Bool.and(u, v) == True{} : Bool}

# the left half is True, so the right is the answer
def and_true(u, _v, eu, ev):
  match u:
    case True{}:
      ev
    case False{}:
      eu

# LAW: a comparison that is at most EQ is not GT
law le_not_gt:
  for c: Cmp
  for e: {Cmp.is_le(c) == True{} : Bool}
  {Cmp.is_gt(c) == False{} : Bool}

# each answer of the comparison
def le_not_gt(c, e):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool}, e)

# LAW: a code point at or below a second, which is below a third, is below
# the third
law u32_le_lt:
  for x: U32
  for a: U32
  for k: U32
  for e: {U32.is_le(x, a) == True{} : Bool}
  for ek: {U32.cmp(a, k) == LT{} : Cmp}
  {U32.cmp(x, k) == LT{} : Cmp}

# a code point is a word of thirty-two bits
def u32_le_lt(x, a, k, e, ek):
  match x a k:
    case U32{+xw} U32{+aw} U32{kw}:
      word_le_lt(32n, xw, aw, kw, le_not_gt(Word.cmp(32n, xw, aw), e), ek)

# LAW: the negation of a bit that answered False
law not_false:
  for u: Bool
  for e: {u == False{} : Bool}
  {Bool.not(u) == True{} : Bool}

# the bit is False, or the premise is a contradiction
def not_false(u, e):
  match u:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd2(&2, {False{} == True{} : Bool}, e)

# ---------------------------------------------------------------------------
# strings with no copy of a char

# LAW: two strings with no copy of a char, one after the other, have none
law clear_append:
  for +a: String
  for +b: String
  for +c: Char
  for +ea: {clear(a, c) == True{} : Bool}
  for eb: {clear(b, c) == True{} : Bool}
  {clear(String.append(a, b), c) == True{} : Bool}

# by induction on the first string
def clear_append(a, b, c, ea, eb):
  match a:
    case SNil{}:
      eb
    case SCon{+h, +t}:
      and_true(Bool.not(Char.is_eq(h, c)), clear(String.append(t, b), c),
        Eq.and.left(Bool.not(Char.is_eq(h, c)), clear(t, c), ea),
        clear_append(t, b, c,
          Eq.and.right(Bool.not(Char.is_eq(h, c)), clear(t, c), ea), eb))

# LAW: the reverse of a string with a last char starts with it
law rev_last:
  for +a: String
  for +c: Char
  for +acc: String
  {String.reverse.go(String.append(a, SCon{c, SNil{}}), acc)
    == SCon{c, String.reverse.go(a, acc)} : String}

# by induction on the string, the accumulator growing
def rev_last(a, c, acc):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      rev_last(t, c, SCon{h, acc})

# LAW: a string holds what the text after it holds
law contains_after:
  for +a: String
  for +b: String
  for +p: String
  for e: {String.contains(b, p) == True{} : Bool}
  {String.contains(String.append(a, b), p) == True{} : Bool}

# one char, with whether the text from it on starts with the pattern given
law contains_after.go:
  for +t: String
  for +b: String
  for +p: String
  for x: Bool
  for ih: {String.contains(String.append(t, b), p) == True{} : Bool}
  {String.contains.if(String.append(t, b), p, x) == True{} : Bool}

def contains_after.go(_t, _b, _p, x, ih):
  match x:
    case True{}:
      {==}
    case False{}:
      ih

# by induction on the text in front, each char with its own arm
def contains_after(a, b, p, e):
  match a:
    case SNil{}:
      e
    case SCon{+h, +t}:
      contains_after.go(t, b, p, String.starts_with(SCon{h, String.append(t, b)}, p),
        contains_after(t, b, p, e))

# ---------------------------------------------------------------------------
# lists of any data

# LAW: a list with nothing after it is the list
law list_append_nil:
  for -A: Data
  for +xs: List<&2, A>
  {List.append(&2, A, xs, []) == xs : List<&2, A>}

# by induction on the list
def list_append_nil(A, xs):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, A>, List<&2, A>, r => h <> r,
        List.append(&2, A, t, []), t, list_append_nil(A, t))

# LAW: appending is associative
law list_append_assoc:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +zs: List<&2, A>
  {List.append(&2, A, List.append(&2, A, xs, ys), zs)
    == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}

# by induction on the first list
def list_append_assoc(A, xs, ys, zs):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, A>, List<&2, A>, r => h <> r,
        List.append(&2, A, List.append(&2, A, t, ys), zs),
        List.append(&2, A, t, List.append(&2, A, ys, zs)),
        list_append_assoc(A, t, ys, zs))

# LAW: reversing onto an accumulator is reversing, then the accumulator
law list_rev_acc:
  for -A: Data
  for +xs: List<&2, A>
  for +acc: List<&2, A>
  {List.reverse.go(&2, A, xs, acc)
    == List.append(&2, A, List.reverse.go(&2, A, xs, []), acc) : List<&2, A>}

# by induction on the list, the accumulator moved to the end
def list_rev_acc(A, xs, acc):
  match xs:
    case []:
      {==}
    case +h <> +t:
      h1 = list_rev_acc(A, t, h <> acc)
      h2 = Equal.sym(List<&2, A>, List.reverse.go(&2, A, t, [h]),
        List.append(&2, A, List.reverse.go(&2, A, t, []), [h]), list_rev_acc(A, t, [h]))
      h3 = Equal.sym(List<&2, A>,
        List.append(&2, A, List.append(&2, A, List.reverse.go(&2, A, t, []), [h]), acc),
        List.append(&2, A, List.reverse.go(&2, A, t, []), h <> acc),
        list_append_assoc(A, List.reverse.go(&2, A, t, []), [h], acc))
      %h2 : {List.reverse.go(&2, A, t, h <> acc) == List.append(&2, A, _, acc) : List<&2, A>}
      %h3 : {List.reverse.go(&2, A, t, h <> acc) == _ : List<&2, A>}
      h1

# LAW: reversing twice gives the list back
law list_rev_rev:
  for -A: Data
  for +xs: List<&2, A>
  for +ys: List<&2, A>
  for +zs: List<&2, A>
  {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, ys), zs)
    == List.reverse.go(&2, A, ys, List.append(&2, A, xs, zs)) : List<&2, A>}

# by induction on the first list: each element goes over and back
def list_rev_rev(A, xs, ys, zs):
  match xs:
    case []:
      {==}
    case +h <> +t:
      list_rev_rev(A, t, h <> ys, zs)

# LAW: two lists of strings with no copy of a char, one after the other, have
# none
law clear_all_append:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +c: Char
  for +ex: {clear.all(xs, c) == True{} : Bool}
  for ey: {clear.all(ys, c) == True{} : Bool}
  {clear.all(List.append(&2, String, xs, ys), c) == True{} : Bool}

# by induction on the first list
def clear_all_append(xs, ys, c, ex, ey):
  match xs:
    case []:
      ey
    case +h <> +t:
      and_true(clear(h, c), clear.all(List.append(&2, String, t, ys), c),
        Eq.and.left(clear(h, c), clear.all(t, c), ex),
        clear_all_append(t, ys, c, Eq.and.right(clear(h, c), clear.all(t, c), ex), ey))

# LAW: a join from a first piece with text in front has the text in front
law join_go_append:
  for +zs: List<&2, String>
  for +x: String
  for +y: String
  for +sep: String
  {String.join.go(zs, String.append(x, y), sep)
    == String.append(x, String.join.go(zs, y, sep)) : String}

# a join with pieces after the first appends the text in front
def join_go_append(zs, x, y, sep):
  match zs:
    case []:
      {==}
    case +z <> +zt:
      Eq.append_assoc(x, y, String.append(sep, String.join.go(zt, z, sep)))

# LAW: a join from a first piece is the piece, then the join from nothing
law join_fold:
  for +zs: List<&2, String>
  for +x: String
  {String.join.go(zs, x, "\n") == String.append(x, String.join.go(zs, "", "\n")) : String}

# the piece is the piece with nothing after it
def join_fold(zs, x):
  a = Eq.append_nil(x)
  %a : {String.join.go(zs, _, "\n") == String.append(x, String.join.go(zs, "", "\n")) : String}
  join_go_append(zs, x, "", "\n")

# LAW: reversing a list with one more at its end puts it first
law list_rev_last:
  for -A: Data
  for +xs: List<&2, A>
  for +x: A
  for +acc: List<&2, A>
  {List.reverse.go(&2, A, List.append(&2, A, xs, [x]), acc)
    == x <> List.reverse.go(&2, A, xs, acc) : List<&2, A>}

# by induction on the list, the accumulator growing
def list_rev_last(A, xs, x, acc):
  match xs:
    case []:
      {==}
    case +h <> +t:
      list_rev_last(A, t, x, h <> acc)

# LAW: dropping nothing from a string leaves it
law drop_zero:
  for +s: String
  {String.drop(s, 0n) == s : String}

# both shapes of the string
def drop_zero(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# LAW: two strings that do not compare equal do not either way round
law eq_flip:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == False{} : Bool}
  {String.eq(b, a) == False{} : Bool}

# the other way round's answer, given as a parameter
law eq_flip.go:
  for +a: String
  for +b: String
  for c: Bool
  for ec: {String.eq(b, a) == c : Bool}
  for e: {String.eq(a, b) == False{} : Bool}
  {c == False{} : Bool}

def eq_flip.go(a, b, c, ec, e):
  match c:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool},
        Equal.trans(Bool, False{}, String.eq(a, b), True{},
          Equal.sym(Bool, String.eq(a, b), False{}, e),
          Equal.trans(Bool, String.eq(a, b), String.eq(a, a), True{},
            Equal.cong(String, Bool, x => String.eq(a, x), b, a, string_eq_true(b, a, ec)),
            Eq.string_eq_self(a))))

# the other way round, asked once
def eq_flip(a, b, e):
  eq_flip.go(a, b, String.eq(b, a), {==}, e)

# The pieces a split leaves. A reader cuts a file at its newlines and a writer
# joins the lines back; the pieces hold no newline, and so a line a rewrite
# builds from them holds none either, which is what lets the file be cut
# again into the same lines.

# LAW: one char of the split, with which way the comparison went given as a
# parameter: a cut adds an empty piece, and a char that is not the separator
# is pushed onto a piece that held none
law split_clear.arm:
  for +h: Char
  for ps: List<&2, String>
  for +c: Char
  for b: Bool
  for eb: {Char.is_eq(h, c) == b : Bool}
  for ih: {clear.all(ps, c) == True{} : Bool}
  {clear.all(String.split.fin(h, ps, b), c) == True{} : Bool}

def split_clear.arm(h, ps, c, b, eb, ih):
  match ps b:
    case Nil{} True{}:
      ih
    case Nil{} False{}:
      %Equal.sym(Bool, Char.is_eq(h, c), False{}, eb)
        : {Bool.and(Bool.and(Bool.not(_), True{}), True{}) == True{} : Bool}
      {==}
    case y <> ys True{}:
      ih
    case y <> ys False{}:
      %Equal.sym(Bool, Char.is_eq(h, c), False{}, eb)
        : {Bool.and(Bool.and(Bool.not(_), clear(y, c)), clear.all(ys, c))
          == True{} : Bool}
      ih

# LAW: no piece of a split holds the separator it was cut at
law split_clear:
  for s: String
  for +c: Char
  {clear.all(String.split(s, c), c) == True{} : Bool}

# by induction on the string, each char with its own arm
def split_clear(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      split_clear.arm(h, String.split(t, c), c, Char.is_eq(h, c), {==},
        split_clear(t, c))

# LAW: an `and` whose first half is the first half of an `and` that answered
# True is the second half's answer
law and_true_left:
  for u: Bool
  for v: Bool
  for eu: {u == True{} : Bool}
  {Bool.and(u, v) == v : Bool}

# the first half is True, so the `and` is its second
def and_true_left(u, _v, eu):
  match u:
    case True{}:
      {==}
    case False{}:
      Eq.bit.absurd(&2, {Bool.and(False{}, _v) == _v : Bool}, eu)

# LAW: where the brackets fall in two `and`s does not change the answer
law and_assoc:
  for u: Bool
  for v: Bool
  for w: Bool
  {Bool.and(u, Bool.and(v, w)) == Bool.and(Bool.and(u, v), w) : Bool}

# by cases on the first bit
def and_assoc(u, _v, _w):
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: two strings joined hold no copy of a char exactly when neither does
law clear_append_eq:
  for a: String
  for +b: String
  for +c: Char
  {clear(String.append(a, b), c) == Bool.and(clear(a, c), clear(b, c)) : Bool}

# by induction on the first string
def clear_append_eq(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      %Equal.sym(Bool, clear(String.append(t, b), c),
        Bool.and(clear(t, c), clear(b, c)), clear_append_eq(t, b, c))
        : {Bool.and(Bool.not(Char.is_eq(h, c)), _)
          == Bool.and(Bool.and(Bool.not(Char.is_eq(h, c)), clear(t, c)),
            clear(b, c)) : Bool}
      and_assoc(Bool.not(Char.is_eq(h, c)), clear(t, c), clear(b, c))

# LAW: what is left of a string with no copy of a char, once its front is
# dropped, holds none either
law drop_clear:
  for s: String
  for n: Nat
  for +c: Char
  for e: {clear(s, c) == True{} : Bool}
  {clear(String.drop(s, n), c) == True{} : Bool}

# by induction on the string, one char dropped at a time
def drop_clear(s, n, c, e):
  match s n:
    case SNil{} _:
      {==}
    case SCon{+h, +t} 0n:
      e
    case SCon{+h, +t} 1n+p:
      drop_clear(t, p, c, Eq.and.right(Bool.not(Char.is_eq(h, c)), clear(t, c), e))

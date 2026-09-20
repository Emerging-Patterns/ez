# check/eq: the Base facts a proof needs and Base does not state. A value
# equals itself: Bend compares strings structurally, and every lookup in this
# repo asks whether a key it just wrote is the key it is looking for, so the
# proofs need that answer to be yes rather than to assume it.
import Base

# LAW: a bit compares equal to itself
law bool_cmp_self:
  for +b: Bool
  {Bool.cmp(b, b) == EQ{} : Cmp}

# the two bits, each compared with itself
def bool_cmp_self(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# LAW: a word compares equal to itself
law word_cmp_self:
  for n: Nat
  for +w: Word(n)
  {Word.cmp(n, w, w) == EQ{} : Cmp}

# by induction on the width: a word of no bits and a bit carried over one
def word_cmp_self(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)),
            Word.cmp.fin(b, b, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, c => Word.cmp.fin(b, b, c),
              Word.cmp(p, t, t), EQ{}, word_cmp_self(p, t)),
            bool_cmp_self(b))

# LAW: a number compares equal to itself
law u32_cmp_self:
  for +u: U32
  {U32.cmp(u, u) == EQ{} : Cmp}

# a number is a word of thirty-two bits, so the word's law answers for it
def u32_cmp_self(u):
  match u:
    case U32{+w}:
      word_cmp_self(32n, w)

# LAW: a char compares equal to itself
law char_cmp_self:
  for +c: Char
  {Char.cmp(c, c) == ((c, c), EQ{}) : (Char & Char) & Cmp}

# a char is a code point, and the pair it is compared inside rides along
def char_cmp_self(c):
  match c:
    case Chr{+x}:
      Equal.cong(Cmp, (Char & Char) & Cmp, r => ((Chr{x}, Chr{x}), r),
        U32.cmp(x, x), EQ{}, u32_cmp_self(x))

# LAW: a string compares equal to itself
law string_cmp_self:
  for +s: String
  {String.cmp(s, s) == ((s, s), EQ{}) : (String & String) & Cmp}

# by induction on the string: the head's law and the tail's, composed the
# way String.cmp composes them
def string_cmp_self(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.trans((String & String) & Cmp,
        String.cmp.fin(t, t, Char.cmp(h, h)),
        String.cmp.rec(h, h, String.cmp(t, t)),
        ((SCon{h, t}, SCon{h, t}), EQ{}),
        Equal.cong((Char & Char) & Cmp, (String & String) & Cmp,
          hc => String.cmp.fin(t, t, hc), Char.cmp(h, h), ((h, h), EQ{}),
          char_cmp_self(h)),
        Equal.cong((String & String) & Cmp, (String & String) & Cmp,
          r => String.cmp.rec(h, h, r), String.cmp(t, t), ((t, t), EQ{}),
          string_cmp_self(t)))

# LAW: a string equals itself. Every lookup in this project turns on it.
law string_eq_self:
  for +s: String
  {String.eq(s, s) == True{} : Bool}

# equality is the comparison read as a bit, so the comparison's law answers
def string_eq_self(s):
  Equal.cong((String & String) & Cmp, Bool, r => String.eq.fin(r),
    String.cmp(s, s), ((s, s), EQ{}), string_cmp_self(s))

# LAW: a char equals itself
law char_eq_self:
  for +c: Char
  {Char.is_eq(c, c) == True{} : Bool}

# and the same for a char
def char_eq_self(c):
  match c:
    case Chr{+x}:
      Equal.cong(Cmp, Bool, r => Cmp.is_eq(r), U32.cmp(x, x), EQ{},
        u32_cmp_self(x))

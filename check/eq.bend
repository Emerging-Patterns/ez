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

# A bit is one thing or the other, never both, so an equation between the two
# holds anything at all. Every proof that lifts a computed condition into a
# parameter reaches an arm the hypothesis has ruled out, and this is how that
# arm is closed. It was written out in pkg/PROOF.bend first; it belongs here,
# beside the other Base facts Base does not state.

# the type that is empty exactly where a bit is True
def bit.emp(flag: Bool) -> Type:
  match flag:
    case False{}:
      Unit
    case True{}:
      Empty

def bit.clash(eq: {False{} == True{} : Bool}) -> Empty:
  %eq : bit.emp(_)
  Unit{}

def bit.gone(a, -A: Kind(a), never: Empty) -> A:
  match never:

def bit.absurd(a, -A: Kind(a), eq: {False{} == True{} : Bool}) -> A:
  bit.gone(a, A, bit.clash(eq))

# and the same read the other way round
def bit.emp2(flag: Bool) -> Type:
  match flag:
    case False{}:
      Empty
    case True{}:
      Unit

def bit.clash2(eq: {True{} == False{} : Bool}) -> Empty:
  %eq : bit.emp2(_)
  Unit{}

def bit.absurd2(a, -A: Kind(a), eq: {True{} == False{} : Bool}) -> A:
  bit.gone(a, A, bit.clash2(eq))

# LAW: the left half of an `and` that answered True
law and.left:
  for u: Bool
  for v: Bool
  for e: {Bool.and(u, v) == True{} : Bool}
  {u == True{} : Bool}

def and.left(u, _v, e):
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

# LAW: every string starts with the empty string
law starts_nil:
  for s: String
  {String.starts_with(s, "") == True{} : Bool}

# the prefix runs out first whatever the string is, so both arms answer True
def starts_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# LAW: one string appended to another leaves the first a prefix of the whole
law starts_append:
  for +a: String
  for b: String
  {String.starts_with(String.append(a, b), a) == True{} : Bool}

# by induction on the prefix, with each character compared against itself
def starts_append(a, b):
  match a:
    case SNil{}:
      starts_nil(b)
    case SCon{+h, +t}:
      Equal.trans(Bool,
        String.starts_with.if(String.append(t, b), t, Char.is_eq(h, h)),
        String.starts_with.if(String.append(t, b), t, True{}),
        True{},
        Equal.cong(Bool, Bool,
          x => String.starts_with.if(String.append(t, b), t, x),
          Char.is_eq(h, h), True{}, char_eq_self(h)),
        starts_append(t, b))

# LAW: nothing appended to a string leaves the string.
law append_nil:
  for s: String
  {String.append(s, SNil{}) == s : String}

# by induction on the string, with each character carried over the tail's law
def append_nil(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x},
        String.append(t, SNil{}), t, append_nil(t))

# LAW: where the brackets fall in a run of appends does not change the run.
# This is what lets the chunk loop drop its accumulator: appending each chunk
# onto what came before it and appending each chunk onto what comes after it
# give the same string, and only the second is linear in the body.
law append_assoc:
  for a: String
  for b: String
  for c: String
  {String.append(String.append(a, b), c)
    == String.append(a, String.append(b, c)) : String}

# by induction on the left string, which is the one both runs copy
def append_assoc(a, b, c):
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x},
        String.append(String.append(t, b), c),
        String.append(t, String.append(b, c)),
        append_assoc(t, b, c))

# check/toml: what the pinned eztoml reader does with what its renderer
# writes. Every law here is stated for all keys, values and table names that
# the reader can take back: a document of tables whose names are not empty,
# whose keys hold no `"`, `=` or newline, and whose names and values hold no
# newline parses back as the tables it was rendered from (`sections_read`).
# eztoml v0.1.0 cuts a pair line at its first `=` even inside a quoted key
# (https://github.com/Emerging-Patterns/eztoml/issues/24, fixed in 0.2.x),
# which is why a key may not hold one. The lock's round trip (EZ-DOC-1,
# lock/PROOF.bend) rests on these, and a ledger's (EZ-LED-4) can.
# check/PROOF.bend puts them through the gate whether or not a proof uses
# them yet.
import Base
import ./eq.bend as Eq
import ./str.bend as Str
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T

# A char a bare key may hold is a letter, a digit, `_` or `-`, and none of
# those is a space: a space is 32 or at most 13, and every one of them is
# above 13. A single code point is ruled out by putting it in; the range by
# `u32_le_lt`.

# LAW: a code point at most 13 is no char a bare key may hold
law low_not_bare:
  for +x: U32
  for +e: {U32.is_le(x, 13) == True{} : Bool}
  {T.bare.at(Chr{x}) == False{} : Bool}

# each range and code point a bare key may hold is above 13
def low_not_bare(x, e):
  h65 = Equal.sym(Cmp, U32.cmp(x, 65), LT{}, Str.u32_le_lt(x, 13, 65, e, {==}))
  h97 = Equal.sym(Cmp, U32.cmp(x, 97), LT{}, Str.u32_le_lt(x, 13, 97, e, {==}))
  h48 = Equal.sym(Cmp, U32.cmp(x, 48), LT{}, Str.u32_le_lt(x, 13, 48, e, {==}))
  h95 = Equal.sym(Cmp, U32.cmp(x, 95), LT{}, Str.u32_le_lt(x, 13, 95, e, {==}))
  h45 = Equal.sym(Cmp, U32.cmp(x, 45), LT{}, Str.u32_le_lt(x, 13, 45, e, {==}))
  %h65 : {Bool.or(Bool.or(Bool.and(Cmp.is_ge(_), U32.is_le(x, 90)),
    Bool.and(U32.is_ge(x, 97), U32.is_le(x, 122))),
    Bool.or(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)),
    Bool.or(U32.is_eq(x, 95), U32.is_eq(x, 45)))) == False{} : Bool}
  %h97 : {Bool.or(Bool.and(Cmp.is_ge(_), U32.is_le(x, 122)),
    Bool.or(Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)),
    Bool.or(U32.is_eq(x, 95), U32.is_eq(x, 45)))) == False{} : Bool}
  %h48 : {Bool.or(Bool.and(Cmp.is_ge(_), U32.is_le(x, 57)),
    Bool.or(U32.is_eq(x, 95), U32.is_eq(x, 45))) == False{} : Bool}
  %h95 : {Bool.or(Cmp.is_eq(_), U32.is_eq(x, 45)) == False{} : Bool}
  %h45 : {Cmp.is_eq(_) == False{} : Bool}
  {==}

# LAW: a char a bare key may hold is none of the chars given, when the char
# given is not one a bare key may hold
law bare_not:
  for +c: Char
  for +d: Char
  for ed: {T.bare.at(d) == False{} : Bool}
  for e: {T.bare.at(c) == True{} : Bool}
  {Char.is_eq(c, d) == False{} : Bool}

# the comparison, given as a parameter: equal chars would make `d` a bare char
law bare_not.go:
  for +c: Char
  for +d: Char
  for b: Bool
  for eb: {Char.is_eq(c, d) == b : Bool}
  for ed: {T.bare.at(d) == False{} : Bool}
  for e: {T.bare.at(c) == True{} : Bool}
  {b == False{} : Bool}

def bare_not.go(c, d, b, eb, ed, e):
  match b:
    case False{}:
      {==}
    case True{}:
      Eq.bit.absurd(&2, {True{} == False{} : Bool},
        Equal.trans(Bool, False{}, T.bare.at(c), True{},
          Equal.trans(Bool, False{}, T.bare.at(d), T.bare.at(c),
            Equal.sym(Bool, T.bare.at(d), False{}, ed),
            Equal.cong(Char, Bool, x => T.bare.at(x), d, c,
              Equal.sym(Char, c, d, Str.char_eq_true(c, d, eb)))),
          e))

# the comparison, asked once
def bare_not(c, d, ed, e):
  bare_not.go(c, d, Char.is_eq(c, d), {==}, ed, e)

# LAW: a char a bare key may hold is not a space
law bare_solid:
  for +c: Char
  for e: {T.bare.at(c) == True{} : Bool}
  {Char.is_space(c) == False{} : Bool}

# the two questions a space asks, given as parameters
law bare_solid.go:
  for +x: U32
  for b1: Bool
  for e1: {U32.is_eq(x, 32) == b1 : Bool}
  for b2: Bool
  for e2: {U32.is_le(x, 13) == b2 : Bool}
  for e: {T.bare.at(Chr{x}) == True{} : Bool}
  {Bool.or(b1, Bool.and(U32.is_ge(x, 9), b2)) == False{} : Bool}

def bare_solid.go(x, b1, e1, b2, e2, e):
  match b1 b2:
    case True{} _:
      Eq.bit.absurd(&2, {True{} == False{} : Bool},
        Equal.trans(Bool, False{}, T.bare.at(Chr{x}), True{},
          Equal.cong(Char, Bool, c => T.bare.at(c), Chr{32}, Chr{x},
            Equal.sym(Char, Chr{x}, Chr{32}, Str.u32_eq(x, 32, e1))),
          e))
    case False{} False{}:
      Str.and_false(U32.is_ge(x, 9))
    case False{} True{}:
      Eq.bit.absurd(&2, {Bool.and(U32.is_ge(x, 9), True{}) == False{} : Bool},
        Equal.trans(Bool, False{}, T.bare.at(Chr{x}), True{},
          Equal.sym(Bool, T.bare.at(Chr{x}), False{}, low_not_bare(x, e2)),
          e))

# a char is a code point
def bare_solid(c, e):
  match c:
    case Chr{+x}:
      bare_solid.go(x, U32.is_eq(x, 32), {==}, U32.is_le(x, 13), {==}, e)

# ---------------------------------------------------------------------------
# trim

# LAW: a trim that has stopped skipping keeps every char, reversed onto what
# it kept already
law walk_kept:
  for +xs: List<&2, Char>
  for +acc: List<&2, Char>
  {T.trim.walk(xs, T.Trim{False{}, acc})
    == T.Trim{False{}, List.reverse.go(&2, Char, xs, acc)} : T.Trim}

# by induction on the chars, each one kept
def walk_kept(xs, acc):
  match xs:
    case []:
      {==}
    case +h <> +t:
      walk_kept(t, h <> acc)

# LAW: a pass of a trim over chars that start with no space keeps them all,
# reversed
law pass_head:
  for +c: Char
  for +xs: List<&2, Char>
  for e: {Char.is_space(c) == False{} : Bool}
  {T.trim.pass(c <> xs) == List.reverse.go(&2, Char, xs, [c]) : List<&2, Char>}

# the first char ends the skipping, and every char after it is kept
def pass_head(c, xs, e):
  f = Equal.sym(Bool, Char.is_space(c), False{}, e)
  %f : {T.trim.out(T.trim.walk(xs, T.trim.keep.go(_, c, [])))
    == List.reverse.go(&2, Char, xs, [c]) : List<&2, Char>}
  Equal.cong(T.Trim, List<&2, Char>, st => T.trim.out(st),
    T.trim.walk(xs, T.Trim{False{}, [c]}),
    T.Trim{False{}, List.reverse.go(&2, Char, xs, [c])},
    walk_kept(xs, [c]))

# LAW: a string that starts and ends with a char that is no space is its own
# trim, whatever it holds between
law trim_ends:
  for +c: Char
  for +m: String
  for +d: Char
  for ec: {Char.is_space(c) == False{} : Bool}
  for ed: {Char.is_space(d) == False{} : Bool}
  {T.trim(SCon{c, String.append(m, SCon{d, SNil{}})})
    == SCon{c, String.append(m, SCon{d, SNil{}})} : String}

# the first pass keeps everything reversed, and so does the second
def trim_ends(c, m, d, ec, ed):
  h1 = Equal.sym(List<&2, Char>,
    String.to_list(String.append(m, SCon{d, SNil{}})),
    List.append(&2, Char, String.to_list(m), [d]),
    Str.to_list_append(m, SCon{d, SNil{}}))
  %h1 : {String.from_list(T.trim.pass(T.trim.pass(c <> _)))
    == SCon{c, String.append(m, SCon{d, SNil{}})} : String}
  h2 = Equal.sym(List<&2, Char>,
    T.trim.pass(c <> List.append(&2, Char, String.to_list(m), [d])),
    List.reverse.go(&2, Char, List.append(&2, Char, String.to_list(m), [d]), [c]),
    pass_head(c, List.append(&2, Char, String.to_list(m), [d]), ec))
  %h2 : {String.from_list(T.trim.pass(_))
    == SCon{c, String.append(m, SCon{d, SNil{}})} : String}
  h3 = Equal.sym(List<&2, Char>,
    List.reverse.go(&2, Char, List.append(&2, Char, String.to_list(m), [d]), [c]),
    List.reverse.go(&2, Char, [d], List.reverse.go(&2, Char, String.to_list(m), [c])),
    Str.rev_append(String.to_list(m), [d], [c]))
  %h3 : {String.from_list(T.trim.pass(_))
    == SCon{c, String.append(m, SCon{d, SNil{}})} : String}
  h4 = Equal.sym(List<&2, Char>,
    T.trim.pass(d <> List.reverse.go(&2, Char, String.to_list(m), [c])),
    List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(m), [c]), [d]),
    pass_head(d, List.reverse.go(&2, Char, String.to_list(m), [c]), ed))
  %h4 : {String.from_list(_) == SCon{c, String.append(m, SCon{d, SNil{}})} : String}
  h5 = Equal.sym(List<&2, Char>,
    List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(m), [c]), [d]),
    List.reverse.go(&2, Char, [c], List.append(&2, Char, String.to_list(m), [d])),
    Str.rev_rev(String.to_list(m), [c], [d]))
  %h5 : {String.from_list(_) == SCon{c, String.append(m, SCon{d, SNil{}})} : String}
  h6 = Equal.sym(String,
    String.from_list(List.append(&2, Char, String.to_list(m), [d])),
    String.append(m, String.from_list([d])),
    Str.from_to_append(m, [d]))
  %h6 : {SCon{c, _} == SCon{c, String.append(m, SCon{d, SNil{}})} : String}
  {==}

# LAW: a space after a string that starts with no space is trimmed away, so
# the two trim alike
law trim_space_after:
  for +c: Char
  for +k: String
  for +ec: {Char.is_space(c) == False{} : Bool}
  {T.trim(SCon{c, String.append(k, " ")}) == T.trim(SCon{c, k}) : String}

# the first pass puts the space first, where the second skips it
def trim_space_after(c, k, ec):
  h1 = Equal.sym(List<&2, Char>,
    String.to_list(String.append(k, " ")),
    List.append(&2, Char, String.to_list(k), [' ']),
    Str.to_list_append(k, " "))
  %h1 : {String.from_list(T.trim.pass(T.trim.pass(c <> _)))
    == T.trim(SCon{c, k}) : String}
  h2 = Equal.sym(List<&2, Char>,
    T.trim.pass(c <> List.append(&2, Char, String.to_list(k), [' '])),
    List.reverse.go(&2, Char, List.append(&2, Char, String.to_list(k), [' ']), [c]),
    pass_head(c, List.append(&2, Char, String.to_list(k), [' ']), ec))
  %h2 : {String.from_list(T.trim.pass(_)) == T.trim(SCon{c, k}) : String}
  h3 = Equal.sym(List<&2, Char>,
    List.reverse.go(&2, Char, List.append(&2, Char, String.to_list(k), [' ']), [c]),
    List.reverse.go(&2, Char, [' '], List.reverse.go(&2, Char, String.to_list(k), [c])),
    Str.rev_append(String.to_list(k), [' '], [c]))
  %h3 : {String.from_list(T.trim.pass(_)) == T.trim(SCon{c, k}) : String}
  h4 = Equal.sym(List<&2, Char>,
    T.trim.pass(c <> String.to_list(k)),
    List.reverse.go(&2, Char, String.to_list(k), [c]),
    pass_head(c, String.to_list(k), ec))
  %h4 : {String.from_list(T.trim.pass(' ' <> List.reverse.go(&2, Char, String.to_list(k), [c])))
    == String.from_list(T.trim.pass(_)) : String}
  {==}

# whether no char of a list is a space. Proof vocabulary.
def solid(cs: List<&2, Char>) -> Bool:
  match cs:
    case []:
      True{}
    case h <> t:
      rest = solid(t)
      Bool.and(Bool.not(Char.is_space(h)), rest)

# LAW: chars that are all solid, reversed onto chars that are, are all solid
law solid_rev:
  for +xs: List<&2, Char>
  for +acc: List<&2, Char>
  for +ex: {solid(xs) == True{} : Bool}
  for ea: {solid(acc) == True{} : Bool}
  {solid(List.reverse.go(&2, Char, xs, acc)) == True{} : Bool}

# by induction on the chars moved onto the accumulator
def solid_rev(xs, acc, ex, ea):
  match xs:
    case []:
      ea
    case +h <> +t:
      solid_rev(t, h <> acc,
        Eq.and.right(Bool.not(Char.is_space(h)), solid(t), ex),
        Str.and_true(Bool.not(Char.is_space(h)), solid(acc),
          Eq.and.left(Bool.not(Char.is_space(h)), solid(t), ex), ea))

# LAW: a pass of a trim over chars that are all solid keeps them all,
# reversed
law pass_solid:
  for +xs: List<&2, Char>
  for e: {solid(xs) == True{} : Bool}
  {T.trim.pass(xs) == List.reverse.go(&2, Char, xs, []) : List<&2, Char>}

# the first char is solid, so nothing is skipped
def pass_solid(xs, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      pass_head(h, t, Eq.not.true(Char.is_space(h),
        Eq.and.left(Bool.not(Char.is_space(h)), solid(t), e)))

# LAW: a string with no space in it is its own trim
law trim_solid:
  for +s: String
  for +e: {solid(String.to_list(s)) == True{} : Bool}
  {T.trim(s) == s : String}

# two passes that keep everything, reversing it twice
def trim_solid(s, e):
  h1 = Equal.sym(List<&2, Char>, T.trim.pass(String.to_list(s)),
    List.reverse.go(&2, Char, String.to_list(s), []),
    pass_solid(String.to_list(s), e))
  %h1 : {String.from_list(T.trim.pass(_)) == s : String}
  h2 = Equal.sym(List<&2, Char>,
    T.trim.pass(List.reverse.go(&2, Char, String.to_list(s), [])),
    List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(s), []), []),
    pass_solid(List.reverse.go(&2, Char, String.to_list(s), []),
      solid_rev(String.to_list(s), [], e, {==})))
  %h2 : {String.from_list(_) == s : String}
  h3 = Equal.sym(List<&2, Char>,
    List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(s), []), []),
    List.append(&2, Char, String.to_list(s), []),
    Str.rev_rev(String.to_list(s), [], []))
  %h3 : {String.from_list(_) == s : String}
  h4 = Equal.sym(List<&2, Char>, List.append(&2, Char, String.to_list(s), []),
    String.to_list(s), Str.list_append_nil(Char, String.to_list(s)))
  %h4 : {String.from_list(_) == s : String}
  Str.from_to(s)

# LAW: a key's chars that a bare key may all hold are all solid
law bare_all_solid:
  for +cs: List<&2, Char>
  for e: {T.bare.all(cs) == True{} : Bool}
  {solid(cs) == True{} : Bool}

# one char, with its answer given as a parameter
law bare_all_solid.go:
  for +c: Char
  for +t: List<&2, Char>
  for b: Bool
  for eb: {T.bare.at(c) == b : Bool}
  for e: {T.bare.all.step(b, _u => T.bare.all(t)) == True{} : Bool}
  for ih: {T.bare.all(t) == True{} : Bool} -> {solid(t) == True{} : Bool}
  {Bool.and(Bool.not(Char.is_space(c)), solid(t)) == True{} : Bool}

def bare_all_solid.go(c, t, b, eb, e, ih):
  match b:
    case True{}:
      Str.and_true(Bool.not(Char.is_space(c)), solid(t),
        Str.not_false(Char.is_space(c), bare_solid(c, eb)), ih(e))
    case False{}:
      Eq.bit.absurd(&2, {Bool.and(Bool.not(Char.is_space(c)), solid(t)) == True{} : Bool}, e)

# by induction on the key's chars
def bare_all_solid(cs, e):
  match cs:
    case []:
      {==}
    case +h <> +t:
      bare_all_solid.go(h, t, T.bare.at(h), {==}, e, x => bare_all_solid(t, x))

# ---------------------------------------------------------------------------
# strip

# LAW: the walk that drops a trailing quote keeps a string with none
law back_clear:
  for +t: String
  for +h: Char
  for e: {Str.clear(SCon{h, t}, '"') == True{} : Bool}
  {T.strip.back.go(String.to_list(t), h, '"') == h <> String.to_list(t)
    : List<&2, Char>}

# by induction on the string, the char behind carried along
def back_clear(t, h, e):
  match t:
    case SNil{}:
      f = Equal.sym(Bool, Char.is_eq(h, '"'), False{},
        Eq.not.true(Char.is_eq(h, '"'),
          Eq.and.left(Bool.not(Char.is_eq(h, '"')), Str.clear(SNil{}, '"'), e)))
      %f : {T.strip.cut(_, h, []) == [h] : List<&2, Char>}
      {==}
    case SCon{+h2, +t2}:
      Equal.cong(List<&2, Char>, List<&2, Char>, r => h <> r,
        T.strip.back.go(String.to_list(t2), h2, '"'),
        h2 <> String.to_list(t2),
        back_clear(t2, h2,
          Eq.and.right(Bool.not(Char.is_eq(h, '"')), Str.clear(SCon{h2, t2}, '"'), e)))

# LAW: a string with no quote in it is its own strip
law strip_clear:
  for +s: String
  for +e: {Str.clear(s, '"') == True{} : Bool}
  {T.strip(s, '"', '"') == s : String}

# the first char is no quote, and nor is the last
def strip_clear(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      f = Equal.sym(Bool, Char.is_eq(h, '"'), False{},
        Eq.not.true(Char.is_eq(h, '"'),
          Eq.and.left(Bool.not(Char.is_eq(h, '"')), Str.clear(t, '"'), e)))
      %f : {String.from_list(T.strip.back(T.strip.cut(_, h, String.to_list(t)), '"'))
        == SCon{h, t} : String}
      g = Equal.sym(List<&2, Char>, T.strip.back.go(String.to_list(t), h, '"'),
        h <> String.to_list(t), back_clear(t, h, e))
      %g : {String.from_list(_) == SCon{h, t} : String}
      Equal.cong(String, String, x => SCon{h, x}, String.from_list(String.to_list(t)), t,
        Str.from_to(t))

# LAW: the walk that drops a trailing char, one char behind the list it
# walks, drops the last one when it is that char
law back_go_char:
  for +t: List<&2, Char>
  for +h: Char
  for +c: Char
  {T.strip.back.go(List.append(&2, Char, t, [c]), h, c) == h <> t
    : List<&2, Char>}

# by induction on the list, the char behind carried along
def back_go_char(t, h, c):
  match t:
    case []:
      f = Equal.sym(Bool, Char.is_eq(c, c), True{}, Eq.char_eq_self(c))
      %f : {h <> T.strip.cut(_, c, []) == [h] : List<&2, Char>}
      {==}
    case +h2 <> +t2:
      Equal.cong(List<&2, Char>, List<&2, Char>, cs => h <> cs,
        T.strip.back.go(List.append(&2, Char, t2, [c]), h2, c),
        h2 <> t2,
        back_go_char(t2, h2, c))

# LAW: a list that ends in a char, with that char dropped
law back_char:
  for +xs: List<&2, Char>
  for +c: Char
  {T.strip.back(List.append(&2, Char, xs, [c]), c) == xs : List<&2, Char>}

# a list with one char is that char, cut
def back_char(xs, c):
  match xs:
    case []:
      f = Equal.sym(Bool, Char.is_eq(c, c), True{}, Eq.char_eq_self(c))
      %f : {T.strip.cut(_, c, []) == [] : List<&2, Char>}
      {==}
    case +h <> +t:
      back_go_char(t, h, c)

# ---------------------------------------------------------------------------
# one line of the lock

# a pair's line, as it is written without its newline. Proof vocabulary.
def pair.line(kv: T.Kv) -> String:
  T.Kv{k, v} = kv
  T.key(k) ++ " = " ++ T.quote(v)

# a table's header line, without its newline
def head.line(name: String) -> String:
  "[" ++ name ++ "]"

# LAW: a pair line whose key starts with no space is its own trim
law trim_line:
  for +c: Char
  for +k: String
  for +v: String
  for ec: {Char.is_space(c) == False{} : Bool}
  {T.trim(SCon{c, String.append(k, " = " ++ T.quote(v))})
    == SCon{c, String.append(k, " = " ++ T.quote(v))} : String}

# the line ends with the value's closing quote
def trim_line(c, k, v, ec):
  h = Eq.append_assoc(k, " = \"" ++ v, "\"")
  %h : {T.trim(SCon{c, _}) == SCon{c, _} : String}
  trim_ends(c, String.append(k, " = \"" ++ v), '"', ec, {==})

# LAW: stripping the quotes off a quoted value gives the value back
law unquote:
  for +v: String
  {T.strip(T.quote(v), '"', '"') == v : String}

# the opening quote is cut, and the closing one is the last char
def unquote(v):
  h1 = Equal.sym(List<&2, Char>, String.to_list(String.append(v, "\"")),
    List.append(&2, Char, String.to_list(v), ['"']), Str.to_list_append(v, "\""))
  %h1 : {String.from_list(T.strip.back(_, '"')) == v : String}
  h2 = Equal.sym(List<&2, Char>,
    T.strip.back(List.append(&2, Char, String.to_list(v), ['"']), '"'),
    String.to_list(v), back_char(String.to_list(v), '"'))
  %h2 : {String.from_list(_) == v : String}
  Str.from_to(v)

# LAW: a pair line, read: its key is whatever the text before its first `=`
# trims and strips to, and its value is the value
law line_of_pair:
  for +c: Char
  for +k: String
  for +v: String
  for eh: {Char.is_eq(c, '#') == False{} : Bool}
  for eb: {Char.is_eq(c, '[') == False{} : Bool}
  for ek: {Str.clear(SCon{c, k}, '=') == True{} : Bool}
  {T.line_of(SCon{c, String.append(k, " = " ++ T.quote(v))})
    == T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'), v}
    : T.Line}

# each question the classifier asks, answered in turn
def line_of_pair(c, k, v, eh, eb, ek):
  f1 = Equal.sym(Bool, Char.is_eq(c, '#'), False{}, eh)
  %f1 : {T.line_of.comment(String.starts_with.if(String.append(k, " = " ++ T.quote(v)),
    SNil{}, _), SCon{c, String.append(k, " = " ++ T.quote(v))})
    == T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'), v} : T.Line}
  f2 = Equal.sym(Bool, Char.is_eq(c, '['), False{}, eb)
  %f2 : {T.line_of.head(String.starts_with.if(String.append(k, " = " ++ T.quote(v)),
    SNil{}, _), SCon{c, String.append(k, " = " ++ T.quote(v))})
    == T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'), v} : T.Line}
  f3 = Equal.sym(Bool,
    String.contains(String.append(SCon{c, k}, " = " ++ T.quote(v)), "="), True{},
    Str.contains_after(SCon{c, k}, " = " ++ T.quote(v), "=", {==}))
  %f3 : {T.line_of.pair(_, SCon{c, String.append(k, " = " ++ T.quote(v))})
    == T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'), v} : T.Line}
  f4 = Equal.sym(List<&2, String>,
    String.split(String.append(SCon{c, k}, " = " ++ T.quote(v)), '='),
    String.append(SCon{c, k}, " ") <> String.split(" " ++ T.quote(v), '='),
    Str.split_front(SCon{c, k}, " = " ++ T.quote(v), '=', " ",
      String.split(" " ++ T.quote(v), '='), ek, {==}))
  %f4 : {T.pair_of(_)
    == T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'), v} : T.Line}
  f5 = Equal.sym(String, String.join(String.split(" " ++ T.quote(v), '='), "="),
    " " ++ T.quote(v), Str.join_split(" " ++ T.quote(v), '='))
  %f5 : {T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'),
    T.strip(T.trim(_), '"', '"')}
    == T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'), v} : T.Line}
  f6 = Equal.sym(String, T.trim(T.quote(v)), T.quote(v), trim_ends('"', v, '"', {==}, {==}))
  %f6 : {T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'),
    T.strip(_, '"', '"')}
    == T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'), v} : T.Line}
  f7 = Equal.sym(String, T.strip(T.quote(v), '"', '"'), v, unquote(v))
  %f7 : {T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'), _}
    == T.LPair{T.strip(T.trim(SCon{c, String.append(k, " ")}), '"', '"'), v} : T.Line}
  {==}

# LAW: a header line, read, opens the table it names and files the one
# before it, whatever the name holds
law step_head:
  for bad: String
  for +name: String
  for +pairs: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +n: String
  {T.step(T.Toml{bad, name, pairs, done}, head.line(n))
    == T.Toml{bad, n, [], T.flush(name, pairs, done)} : T.Toml}

# each question the classifier asks, answered in turn
def step_head(bad, name, pairs, done, n):
  t1 = Equal.sym(String, T.trim(SCon{'[', String.append(n, "]")}),
    SCon{'[', String.append(n, "]")}, trim_ends('[', n, ']', {==}, {==}))
  %t1 : {T.step.go(T.Toml{bad, name, pairs, done}, T.line_of(_))
    == T.Toml{bad, n, [], T.flush(name, pairs, done)} : T.Toml}
  t2 = Equal.sym(Bool, String.starts_with(String.append(n, "]"), ""), True{},
    Eq.starts_nil(String.append(n, "]")))
  %t2 : {T.step.go(T.Toml{bad, name, pairs, done},
    T.line_of.head(_, SCon{'[', String.append(n, "]")}))
    == T.Toml{bad, n, [], T.flush(name, pairs, done)} : T.Toml}
  t3 = Equal.sym(String, String.reverse.go(String.append(n, "]"), "["),
    SCon{']', String.reverse.go(n, "[")}, Str.rev_last(n, ']', "["))
  %t3 : {T.step.go(T.Toml{bad, name, pairs, done},
    T.head_of(SCon{'[', String.append(n, "]")}, String.starts_with(_, "]")))
    == T.Toml{bad, n, [], T.flush(name, pairs, done)} : T.Toml}
  t4 = Equal.sym(Bool, String.starts_with(String.reverse.go(n, "["), ""), True{},
    Eq.starts_nil(String.reverse.go(n, "[")))
  %t4 : {T.step.go(T.Toml{bad, name, pairs, done},
    T.head_of(SCon{'[', String.append(n, "]")}, _))
    == T.Toml{bad, n, [], T.flush(name, pairs, done)} : T.Toml}
  t5 = Equal.sym(List<&2, Char>, String.to_list(String.append(n, "]")),
    List.append(&2, Char, String.to_list(n), [']']), Str.to_list_append(n, "]"))
  %t5 : {T.Toml{bad, String.from_list(T.strip.back(_, ']')), [], T.flush(name, pairs, done)}
    == T.Toml{bad, n, [], T.flush(name, pairs, done)} : T.Toml}
  t6 = Equal.sym(List<&2, Char>,
    T.strip.back(List.append(&2, Char, String.to_list(n), [']']), ']'),
    String.to_list(n), back_char(String.to_list(n), ']'))
  %t6 : {T.Toml{bad, String.from_list(_), [], T.flush(name, pairs, done)}
    == T.Toml{bad, n, [], T.flush(name, pairs, done)} : T.Toml}
  t7 = Equal.sym(String, String.from_list(String.to_list(n)), n, Str.from_to(n))
  %t7 : {T.Toml{bad, _, [], T.flush(name, pairs, done)}
    == T.Toml{bad, n, [], T.flush(name, pairs, done)} : T.Toml}
  {==}

# LAW: a scan step that answered True had a head that answered True
law all_head:
  for x: Bool
  for r: Unit -> Bool
  for e: {T.bare.all.step(x, r) == True{} : Bool}
  {x == True{} : Bool}

# the head that answered False ends the scan
def all_head(x, _r, e):
  match x:
    case True{}:
      {==}
    case False{}:
      e

# LAW: the first char of a bare key is solid
law bare_head_solid:
  for +c: Char
  for +t: String
  for e: {T.bare(SCon{c, t}) == True{} : Bool}
  {Char.is_space(c) == False{} : Bool}

# the key's chars are all solid, the first among them
def bare_head_solid(c, t, e):
  Eq.not.true(Char.is_space(c),
    Eq.and.left(Bool.not(Char.is_space(c)), solid(String.to_list(t)),
      bare_all_solid(String.to_list(SCon{c, t}),
        Eq.and.right(Bool.not(String.is_empty(SCon{c, t})),
          T.bare.all(String.to_list(SCon{c, t})), e))))

# LAW: and a char a bare key may hold
law bare_head_at:
  for +c: Char
  for +t: String
  for e: {T.bare(SCon{c, t}) == True{} : Bool}
  {T.bare.at(c) == True{} : Bool}

# the scan's first step
def bare_head_at(c, t, e):
  all_head(T.bare.at(c), _u => T.bare.all(String.to_list(t)),
    Eq.and.right(Bool.not(String.is_empty(SCon{c, t})),
      T.bare.all(String.to_list(SCon{c, t})), e))

# LAW: a bare key's chars are all solid
law bare_solid_all:
  for +k: String
  for e: {T.bare(k) == True{} : Bool}
  {solid(String.to_list(k)) == True{} : Bool}

# a bare key's chars are ones a bare key may hold
def bare_solid_all(k, e):
  bare_all_solid(String.to_list(k),
    Eq.and.right(Bool.not(String.is_empty(k)), T.bare.all(String.to_list(k)), e))

# LAW: a pair line of a bare key, read into a table being filled, is the pair
law step_pair.bare:
  for bad: String
  for +n: String
  for acc: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for +k: String
  for +v: String
  for +eb: {T.bare(k) == True{} : Bool}
  for en: {String.is_empty(n) == False{} : Bool}
  for ek1: {Str.clear(k, '=') == True{} : Bool}
  for ek2: {Str.clear(k, '"') == True{} : Bool}
  {T.step(T.Toml{bad, n, acc, done}, String.append(k, " = " ++ T.quote(v)))
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}

def step_pair.bare(bad, n, acc, done, k, v, eb, en, ek1, ek2):
  match k:
    case SNil{}:
      Eq.bit.absurd(&2, {T.step(T.Toml{bad, n, acc, done}, String.append(SNil{}, " = " ++ T.quote(v)))
        == T.Toml{bad, n, T.Kv{SNil{}, v} <> acc, done} : T.Toml}, eb)
    case SCon{+c, +t}:
      t1 = Equal.sym(String, T.trim(SCon{c, String.append(t, " = " ++ T.quote(v))}),
        SCon{c, String.append(t, " = " ++ T.quote(v))},
        trim_line(c, t, v, bare_head_solid(c, t, eb)))
      %t1 : {T.step.go(T.Toml{bad, n, acc, done}, T.line_of(_))
        == T.Toml{bad, n, T.Kv{SCon{c, t}, v} <> acc, done} : T.Toml}
      t2 = Equal.sym(T.Line, T.line_of(SCon{c, String.append(t, " = " ++ T.quote(v))}),
        T.LPair{T.strip(T.trim(SCon{c, String.append(t, " ")}), '"', '"'), v},
        line_of_pair(c, t, v, bare_not(c, '#', {==}, bare_head_at(c, t, eb)),
          bare_not(c, '[', {==}, bare_head_at(c, t, eb)),
          ek1))
      %t2 : {T.step.go(T.Toml{bad, n, acc, done}, _)
        == T.Toml{bad, n, T.Kv{SCon{c, t}, v} <> acc, done} : T.Toml}
      t3 = Equal.sym(Bool, String.is_empty(n), False{}, en)
      %t3 : {T.put.go(_, bad, n, acc, done,
        T.strip(T.trim(SCon{c, String.append(t, " ")}), '"', '"'), v)
        == T.Toml{bad, n, T.Kv{SCon{c, t}, v} <> acc, done} : T.Toml}
      t4 = Equal.sym(String, T.trim(SCon{c, String.append(t, " ")}),
        T.trim(SCon{c, t}), trim_space_after(c, t, bare_head_solid(c, t, eb)))
      %t4 : {T.Toml{bad, n, T.Kv{T.strip(_, '"', '"'), v} <> acc, done}
        == T.Toml{bad, n, T.Kv{SCon{c, t}, v} <> acc, done} : T.Toml}
      t5 = Equal.sym(String, T.trim(SCon{c, t}), SCon{c, t},
        trim_solid(SCon{c, t}, bare_solid_all(SCon{c, t}, eb)))
      %t5 : {T.Toml{bad, n, T.Kv{T.strip(_, '"', '"'), v} <> acc, done}
        == T.Toml{bad, n, T.Kv{SCon{c, t}, v} <> acc, done} : T.Toml}
      t6 = Equal.sym(String, T.strip(SCon{c, t}, '"', '"'), SCon{c, t},
        strip_clear(SCon{c, t}, ek2))
      %t6 : {T.Toml{bad, n, T.Kv{_, v} <> acc, done}
        == T.Toml{bad, n, T.Kv{SCon{c, t}, v} <> acc, done} : T.Toml}
      {==}

# LAW: a pair line of a quoted key, read into a table being filled, is the
# pair
law step_pair.quoted:
  for bad: String
  for +n: String
  for acc: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for +k: String
  for +v: String
  for en: {String.is_empty(n) == False{} : Bool}
  for ek1: {Str.clear(k, '=') == True{} : Bool}
  {T.step(T.Toml{bad, n, acc, done}, String.append(T.quote(k), " = " ++ T.quote(v)))
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}

def step_pair.quoted(bad, n, acc, done, k, v, en, ek1):
  t1 = Equal.sym(String,
    T.trim(SCon{'"', String.append(String.append(k, "\""), " = " ++ T.quote(v))}),
    SCon{'"', String.append(String.append(k, "\""), " = " ++ T.quote(v))},
    trim_line('"', String.append(k, "\""), v, {==}))
  %t1 : {T.step.go(T.Toml{bad, n, acc, done}, T.line_of(_))
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}
  t2 = Equal.sym(T.Line,
    T.line_of(SCon{'"', String.append(String.append(k, "\""), " = " ++ T.quote(v))}),
    T.LPair{T.strip(T.trim(SCon{'"', String.append(String.append(k, "\""), " ")}),
      '"', '"'), v},
    line_of_pair('"', String.append(k, "\""), v, {==}, {==},
      Str.clear_append(k, "\"", '=', ek1, {==})))
  %t2 : {T.step.go(T.Toml{bad, n, acc, done}, _)
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}
  t3 = Equal.sym(Bool, String.is_empty(n), False{}, en)
  %t3 : {T.put.go(_, bad, n, acc, done,
    T.strip(T.trim(SCon{'"', String.append(String.append(k, "\""), " ")}), '"', '"'), v)
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}
  t4 = Equal.sym(String,
    T.trim(SCon{'"', String.append(String.append(k, "\""), " ")}),
    T.trim(T.quote(k)), trim_space_after('"', String.append(k, "\""), {==}))
  %t4 : {T.Toml{bad, n, T.Kv{T.strip(_, '"', '"'), v} <> acc, done}
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}
  t5 = Equal.sym(String, T.trim(T.quote(k)), T.quote(k),
    trim_ends('"', k, '"', {==}, {==}))
  %t5 : {T.Toml{bad, n, T.Kv{T.strip(_, '"', '"'), v} <> acc, done}
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}
  t6 = Equal.sym(String, T.strip(T.quote(k), '"', '"'), k, unquote(k))
  %t6 : {T.Toml{bad, n, T.Kv{_, v} <> acc, done}
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}
  {==}

# the key's two spellings, with which one it is given as a parameter
law step_pair.go:
  for bad: String
  for +n: String
  for acc: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for +k: String
  for +v: String
  for b: Bool
  for eb: {T.bare(k) == b : Bool}
  for en: {String.is_empty(n) == False{} : Bool}
  for ek1: {Str.clear(k, '=') == True{} : Bool}
  for ek2: {Str.clear(k, '"') == True{} : Bool}
  {T.step(T.Toml{bad, n, acc, done},
    String.append(Bool.pick(String, b, k, T.quote(k)), " = " ++ T.quote(v)))
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}

def step_pair.go(bad, n, acc, done, k, v, b, eb, en, ek1, ek2):
  match b:
    case True{}:
      step_pair.bare(bad, n, acc, done, k, v, eb, en, ek1, ek2)
    case False{}:
      step_pair.quoted(bad, n, acc, done, k, v, en, ek1)

# LAW: a pair line, read into a table being filled, adds the pair it was
# written from, when its key holds no `"` and no `=`
law step_pair:
  for bad: String
  for +n: String
  for acc: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for +k: String
  for +v: String
  for en: {String.is_empty(n) == False{} : Bool}
  for ek1: {Str.clear(k, '=') == True{} : Bool}
  for ek2: {Str.clear(k, '"') == True{} : Bool}
  {T.step(T.Toml{bad, n, acc, done}, pair.line(T.Kv{k, v}))
    == T.Toml{bad, n, T.Kv{k, v} <> acc, done} : T.Toml}

# which spelling the key has, asked once
def step_pair(bad, n, acc, done, k, v, en, ek1, ek2):
  step_pair.go(bad, n, acc, done, k, v, T.bare(k), {==}, en, ek1, ek2)

# ---------------------------------------------------------------------------
# a document as lines

# every pair's line. Proof vocabulary.
def pair.lines(ps: List<&2, T.Kv>) -> List<&2, String>:
  match ps:
    case []:
      []
    case h <> t:
      pair.line(h) <> pair.lines(t)

# lines, each ended by a newline
def unlines(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> t:
      String.append(h, SCon{'\n', unlines(t)})

# the lines of a document: each table's header, its pairs, and a blank line
def doc.lines(ss: List<&2, T.Sect>) -> List<&2, String>:
  match ss:
    case []:
      []
    case T.Sect{n, ps} <> t:
      head.line(n) <> List.append(&2, String, pair.lines(ps), "" <> doc.lines(t))

# LAW: a table's pairs render as their lines, each ended by a newline
law render_pairs:
  for +ps: List<&2, T.Kv>
  {T.render.pairs(ps) == unlines(pair.lines(ps)) : String}

# by induction on the pairs, each line reassociated
def render_pairs(ps):
  match ps:
    case []:
      {==}
    case T.Kv{+k, +v} <> +t:
      ih = Equal.sym(String, T.render.pairs(t), unlines(pair.lines(t)), render_pairs(t))
      %ih : {String.append(T.render.pair(T.Kv{k, v}), _)
        == String.append(pair.line(T.Kv{k, v}), SCon{'\n', unlines(pair.lines(t))}) : String}
      e1 = Equal.sym(String,
        String.append(String.append(T.key(k), " = " ++ T.quote(v) ++ "\n"), unlines(pair.lines(t))),
        String.append(T.key(k), String.append(" = " ++ T.quote(v) ++ "\n", unlines(pair.lines(t)))),
        Eq.append_assoc(T.key(k), " = " ++ T.quote(v) ++ "\n", unlines(pair.lines(t))))
      %e1 : {_ == String.append(pair.line(T.Kv{k, v}), SCon{'\n', unlines(pair.lines(t))}) : String}
      e2 = Equal.sym(String,
        String.append(String.append(T.key(k), " = " ++ T.quote(v)), SCon{'\n', unlines(pair.lines(t))}),
        String.append(T.key(k), String.append(" = " ++ T.quote(v), SCon{'\n', unlines(pair.lines(t))})),
        Eq.append_assoc(T.key(k), " = " ++ T.quote(v), SCon{'\n', unlines(pair.lines(t))}))
      %e2 : {String.append(T.key(k), String.append(" = " ++ T.quote(v) ++ "\n", unlines(pair.lines(t))))
        == _ : String}
      e3 = Equal.sym(String,
        String.append(String.append(String.append(v, "\""), "\n"), unlines(pair.lines(t))),
        String.append(String.append(v, "\""), SCon{'\n', unlines(pair.lines(t))}),
        Eq.append_assoc(String.append(v, "\""), "\n", unlines(pair.lines(t))))
      %e3 : {String.append(T.key(k), SCon{' ', SCon{'=', SCon{' ', SCon{'"', _}}}})
        == String.append(T.key(k), String.append(" = " ++ T.quote(v), SCon{'\n', unlines(pair.lines(t))}))
        : String}
      {==}

# LAW: a table renders as its header and pair lines, each ended by a newline
law render_sect:
  for +n: String
  for +ps: List<&2, T.Kv>
  {T.render.sect(T.Sect{n, ps}) == unlines(head.line(n) <> pair.lines(ps)) : String}

# the pairs' text, then the header reassociated
def render_sect(n, ps):
  r = Equal.sym(String, T.render.pairs(ps), unlines(pair.lines(ps)), render_pairs(ps))
  %r : {SCon{'[', String.append(n, SCon{']', SCon{'\n', _}})}
    == unlines(head.line(n) <> pair.lines(ps)) : String}
  a = Equal.sym(String,
    String.append(String.append(n, "]"), SCon{'\n', unlines(pair.lines(ps))}),
    String.append(n, SCon{']', SCon{'\n', unlines(pair.lines(ps))}}),
    Eq.append_assoc(n, "]", SCon{'\n', unlines(pair.lines(ps))}))
  %a : {SCon{'[', String.append(n, SCon{']', SCon{'\n', unlines(pair.lines(ps))}})}
    == SCon{'[', _} : String}
  {==}

# LAW: lines joined by newlines, up to a blank one, are those lines each ended
# by a newline, then whatever the join gives after the blank
law join_lines:
  for +xs: List<&2, String>
  for +x: String
  for +ts: List<&2, String>
  {String.join.go(List.append(&2, String, xs, "" <> ts), x, "\n")
    == String.append(unlines(x <> xs), String.join.go(ts, "", "\n")) : String}

# by induction on the lines
def join_lines(xs, x, ts):
  match xs:
    case []:
      Equal.sym(String,
        String.append(String.append(x, "\n"), String.join.go(ts, "", "\n")),
        String.append(x, SCon{'\n', String.join.go(ts, "", "\n")}),
        Eq.append_assoc(x, "\n", String.join.go(ts, "", "\n")))
    case +y <> +ys:
      ih = Equal.sym(String,
        String.join.go(List.append(&2, String, ys, "" <> ts), y, "\n"),
        String.append(unlines(y <> ys), String.join.go(ts, "", "\n")),
        join_lines(ys, y, ts))
      %ih : {String.append(x, SCon{'\n', _})
        == String.append(unlines(x <> y <> ys), String.join.go(ts, "", "\n")) : String}
      a = Equal.sym(String,
        String.append(String.append(x, SCon{'\n', unlines(y <> ys)}), String.join.go(ts, "", "\n")),
        String.append(x, String.append(SCon{'\n', unlines(y <> ys)}, String.join.go(ts, "", "\n"))),
        Eq.append_assoc(x, SCon{'\n', unlines(y <> ys)}, String.join.go(ts, "", "\n")))
      %a : {String.append(x, SCon{'\n', String.append(unlines(y <> ys), String.join.go(ts, "", "\n"))})
        == _ : String}
      {==}

# LAW: a rendered table, joined to the tables after it, is its text, then
# what the join of their lines gives after a blank line
law render_lines.rest:
  for +r: String
  for +t: List<&2, T.Sect>
  for ih: {T.render(t) == String.join(doc.lines(t), "\n") : String}
  {String.join.go(T.render.all(t), r, "\n")
    == String.append(r, String.join.go(doc.lines(t), "", "\n")) : String}

def render_lines.rest(r, t, ih):
  match t:
    case []:
      Equal.sym(String, String.append(r, ""), r, Eq.append_nil(r))
    case T.Sect{+n, +ps} <> +t2:
      Equal.cong(String, String, x => String.append(r, SCon{'\n', x}),
        T.render(T.Sect{n, ps} <> t2), String.join(doc.lines(T.Sect{n, ps} <> t2), "\n"), ih)

# LAW: a document renders as its lines joined by newlines
law render_lines:
  for +ss: List<&2, T.Sect>
  {T.render(ss) == String.join(doc.lines(ss), "\n") : String}

# by induction on the tables
def render_lines(ss):
  match ss:
    case []:
      {==}
    case T.Sect{+n, +ps} <> +t:
      j = Equal.sym(String,
        String.join.go(List.append(&2, String, pair.lines(ps), "" <> doc.lines(t)), head.line(n), "\n"),
        String.append(unlines(head.line(n) <> pair.lines(ps)), String.join.go(doc.lines(t), "", "\n")),
        join_lines(pair.lines(ps), head.line(n), doc.lines(t)))
      %j : {String.join.go(T.render.all(t), T.render.sect(T.Sect{n, ps}), "\n") == _ : String}
      s = render_sect(n, ps)
      %s : {String.join.go(T.render.all(t), T.render.sect(T.Sect{n, ps}), "\n")
        == String.append(_, String.join.go(doc.lines(t), "", "\n")) : String}
      render_lines.rest(T.render.sect(T.Sect{n, ps}), t, render_lines(t))

# ---------------------------------------------------------------------------
# reading the lines back

# whether a pair reads back as itself: its key holds no `=`, no `"` and no
# newline, and its value no newline. Proof vocabulary.
def kv.ok(kv: T.Kv) -> Bool:
  T.Kv{+k, v} = kv
  Bool.and(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
    Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))))

# whether every pair of a table does
def kvs.ok(ps: List<&2, T.Kv>) -> Bool:
  match ps:
    case []:
      True{}
    case h <> t:
      rest = kvs.ok(t)
      Bool.and(kv.ok(h), rest)

# whether a table does: its name is not empty and holds no newline, and every
# pair does
def sect.ok(table: T.Sect) -> Bool:
  T.Sect{+n, ps} = table
  Bool.and(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), kvs.ok(ps)))

# whether every table of a document does
def sects.ok(ss: List<&2, T.Sect>) -> Bool:
  match ss:
    case []:
      True{}
    case h <> t:
      rest = sects.ok(t)
      Bool.and(sect.ok(h), rest)

# LAW: a table's pair lines, read into it, add its pairs, reversed
law walk_pairs:
  for +ps: List<&2, T.Kv>
  for +rest: List<&2, String>
  for +bad: String
  for +n: String
  for +acc: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +en: {String.is_empty(n) == False{} : Bool}
  for +eok: {kvs.ok(ps) == True{} : Bool}
  {T.parse.walk(List.append(&2, String, pair.lines(ps), rest), T.Toml{bad, n, acc, done})
    == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv, ps, acc), done})
    : T.Toml}

# by induction on the pairs, each one read
def walk_pairs(ps, rest, bad, n, acc, done, en, eok):
  match ps:
    case []:
      {==}
    case T.Kv{+k, +v} <> +t:
      ok = Eq.and.left(kv.ok(T.Kv{k, v}), kvs.ok(t), eok)
      ek1 = Eq.and.left(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
        Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))), ok)
      ok2 = Eq.and.right(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
        Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))),
        Eq.and.left(kv.ok(T.Kv{k, v}), kvs.ok(t), eok))
      ek2 = Eq.and.left(Str.clear(k, '"'), Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')), ok2)
      s = Equal.sym(T.Toml, T.step(T.Toml{bad, n, acc, done}, pair.line(T.Kv{k, v})),
        T.Toml{bad, n, T.Kv{k, v} <> acc, done},
        step_pair(bad, n, acc, done, k, v, en, ek1, ek2))
      %s : {T.parse.walk(List.append(&2, String, pair.lines(t), rest), _)
        == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv, t, T.Kv{k, v} <> acc), done})
        : T.Toml}
      walk_pairs(t, rest, bad, n, T.Kv{k, v} <> acc, done, en,
        Eq.and.right(kv.ok(T.Kv{k, v}), kvs.ok(t), eok))

# LAW: a table's lines, read, fill it and file the one before it
law walk_sect:
  for +n: String
  for +ps: List<&2, T.Kv>
  for +t: List<&2, T.Sect>
  for +bad: String
  for +name: String
  for +pairs: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +en: {String.is_empty(n) == False{} : Bool}
  for +eok: {kvs.ok(ps) == True{} : Bool}
  {T.parse.walk(doc.lines(T.Sect{n, ps} <> t), T.Toml{bad, name, pairs, done})
    == T.parse.walk(doc.lines(t),
      T.Toml{bad, n, List.reverse.go(&2, T.Kv, ps, []), T.flush(name, pairs, done)})
    : T.Toml}

# the header, then the pairs; the blank line changes nothing
def walk_sect(n, ps, t, bad, name, pairs, done, en, eok):
  h = Equal.sym(T.Toml, T.step(T.Toml{bad, name, pairs, done}, head.line(n)),
    T.Toml{bad, n, [], T.flush(name, pairs, done)}, step_head(bad, name, pairs, done, n))
  %h : {T.parse.walk(List.append(&2, String, pair.lines(ps), "" <> doc.lines(t)), _)
    == T.parse.walk(doc.lines(t),
      T.Toml{bad, n, List.reverse.go(&2, T.Kv, ps, []), T.flush(name, pairs, done)})
    : T.Toml}
  walk_pairs(ps, "" <> doc.lines(t), bad, n, [], T.flush(name, pairs, done), en, eok)

# LAW: the tables filed so far, once one more is filed and they are put back
# in order, are the ones before it and then it
law flush_filed:
  for +n: String
  for +ps: List<&2, T.Kv>
  for +filed: List<&2, T.Sect>
  for +t: List<&2, T.Sect>
  for en: {String.is_empty(n) == False{} : Bool}
  {List.append(&2, T.Sect,
    List.reverse(&2, T.Sect, T.flush(n, List.reverse.go(&2, T.Kv, ps, []), filed)), t)
    == List.append(&2, T.Sect, List.reverse(&2, T.Sect, filed), T.Sect{n, ps} <> t)
    : List<&2, T.Sect>}

# the pairs were reversed twice, and the table goes after the filed ones
def flush_filed(n, ps, filed, t, en):
  f = Equal.sym(Bool, String.is_empty(n), False{}, en)
  %f : {List.append(&2, T.Sect, List.reverse(&2, T.Sect,
    T.flush.put(_, n, List.reverse.go(&2, T.Kv, ps, []), filed)), t)
    == List.append(&2, T.Sect, List.reverse(&2, T.Sect, filed), T.Sect{n, ps} <> t)
    : List<&2, T.Sect>}
  rr = Equal.sym(List<&2, T.Kv>,
    List.reverse.go(&2, T.Kv, List.reverse.go(&2, T.Kv, ps, []), []), ps,
    Equal.trans(List<&2, T.Kv>,
      List.reverse.go(&2, T.Kv, List.reverse.go(&2, T.Kv, ps, []), []),
      List.append(&2, T.Kv, ps, []), ps,
      Str.list_rev_rev(T.Kv, ps, [], []), Str.list_append_nil(T.Kv, ps)))
  %rr : {List.append(&2, T.Sect, List.reverse(&2, T.Sect, T.Sect{n, _} <> filed), t)
    == List.append(&2, T.Sect, List.reverse(&2, T.Sect, filed), T.Sect{n, ps} <> t)
    : List<&2, T.Sect>}
  r3 = Equal.sym(List<&2, T.Sect>,
    List.reverse.go(&2, T.Sect, filed, [T.Sect{n, ps}]),
    List.append(&2, T.Sect, List.reverse.go(&2, T.Sect, filed, []),
      [T.Sect{n, ps}]),
    Str.list_rev_acc(T.Sect, filed,
      [T.Sect{n, ps}]))
  %r3 : {List.append(&2, T.Sect, _, t)
    == List.append(&2, T.Sect, List.reverse(&2, T.Sect, filed),
      T.Sect{n, ps} <> t)
    : List<&2, T.Sect>}
  Str.list_append_assoc(T.Sect, List.reverse.go(&2, T.Sect, filed, []),
    [T.Sect{n, ps}], t)

# LAW: a document's lines, read from any state with no error, file the
# tables it already filed and then every table the document holds
law walk_doc:
  for +ss: List<&2, T.Sect>
  for +bad: String
  for +name: String
  for +pairs: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +eok: {sects.ok(ss) == True{} : Bool}
  {T.parse.fin(T.parse.walk(doc.lines(ss), T.Toml{bad, name, pairs, done}))
    == T.Toml{bad, "", [], List.append(&2, T.Sect,
      List.reverse(&2, T.Sect, T.flush(name, pairs, done)), ss)} : T.Toml}

# by induction on the tables
def walk_doc(ss, bad, name, pairs, done, eok):
  match ss:
    case []:
      Equal.cong(List<&2, T.Sect>, T.Toml, x => T.Toml{bad, "", [], x},
        List.reverse(&2, T.Sect, T.flush(name, pairs, done)),
        List.append(&2, T.Sect, List.reverse(&2, T.Sect, T.flush(name, pairs, done)), []),
        Equal.sym(List<&2, T.Sect>,
          List.append(&2, T.Sect, List.reverse(&2, T.Sect, T.flush(name, pairs, done)), []),
          List.reverse(&2, T.Sect, T.flush(name, pairs, done)),
          Str.list_append_nil(T.Sect, List.reverse(&2, T.Sect, T.flush(name, pairs, done)))))
    case T.Sect{+n, +ps} <> +t:
      ok = Eq.and.left(sect.ok(T.Sect{n, ps}), sects.ok(t), eok)
      en = Eq.not.true(String.is_empty(n), Eq.and.left(Bool.not(String.is_empty(n)),
        Bool.and(Str.clear(n, '\n'), kvs.ok(ps)), ok))
      ep = Eq.and.right(Str.clear(n, '\n'), kvs.ok(ps),
        Eq.and.right(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), kvs.ok(ps)),
          Eq.and.left(sect.ok(T.Sect{n, ps}), sects.ok(t), eok)))
      w = Equal.sym(T.Toml,
        T.parse.walk(doc.lines(T.Sect{n, ps} <> t), T.Toml{bad, name, pairs, done}),
        T.parse.walk(doc.lines(t),
          T.Toml{bad, n, List.reverse.go(&2, T.Kv, ps, []), T.flush(name, pairs, done)}),
        walk_sect(n, ps, t, bad, name, pairs, done, en, ep))
      %w : {T.parse.fin(_) == T.Toml{bad, "", [], List.append(&2, T.Sect,
        List.reverse(&2, T.Sect, T.flush(name, pairs, done)), T.Sect{n, ps} <> t)} : T.Toml}
      Equal.trans(T.Toml,
        T.parse.fin(T.parse.walk(doc.lines(t),
          T.Toml{bad, n, List.reverse.go(&2, T.Kv, ps, []), T.flush(name, pairs, done)})),
        T.Toml{bad, "", [], List.append(&2, T.Sect, List.reverse(&2, T.Sect,
          T.flush(n, List.reverse.go(&2, T.Kv, ps, []), T.flush(name, pairs, done))), t)},
        T.Toml{bad, "", [], List.append(&2, T.Sect,
          List.reverse(&2, T.Sect, T.flush(name, pairs, done)), T.Sect{n, ps} <> t)},
        walk_doc(t, bad, n, List.reverse.go(&2, T.Kv, ps, []), T.flush(name, pairs, done),
          Eq.and.right(sect.ok(T.Sect{n, ps}), sects.ok(t), eok)),
        Equal.cong(List<&2, T.Sect>, T.Toml, x => T.Toml{bad, "", [], x},
          List.append(&2, T.Sect, List.reverse(&2, T.Sect,
            T.flush(n, List.reverse.go(&2, T.Kv, ps, []), T.flush(name, pairs, done))), t),
          List.append(&2, T.Sect,
            List.reverse(&2, T.Sect, T.flush(name, pairs, done)), T.Sect{n, ps} <> t),
          flush_filed(n, ps, T.flush(name, pairs, done), t,
            Eq.not.true(String.is_empty(n), Eq.and.left(Bool.not(String.is_empty(n)),
              Bool.and(Str.clear(n, '\n'), kvs.ok(ps)),
              Eq.and.left(sect.ok(T.Sect{n, ps}), sects.ok(t), eok))))))

# LAW: a key, spelled either way, holds no newline when the key holds none
law key_clear.go:
  for +k: String
  for b: Bool
  for +e: {Str.clear(k, '\n') == True{} : Bool}
  {Str.clear(Bool.pick(String, b, k, T.quote(k)), '\n') == True{} : Bool}

def key_clear.go(k, b, e):
  match b:
    case True{}:
      e
    case False{}:
      Str.clear_append(k, "\"", '\n', e, {==})

# LAW: every pair line of a table that reads back holds no newline
law pairs_clear:
  for +ps: List<&2, T.Kv>
  for +eok: {kvs.ok(ps) == True{} : Bool}
  {Str.clear.all(pair.lines(ps), '\n') == True{} : Bool}

# by induction on the pairs
def pairs_clear(ps, eok):
  match ps:
    case []:
      {==}
    case T.Kv{+k, +v} <> +t:
      ok = Eq.and.left(kv.ok(T.Kv{k, v}), kvs.ok(t), eok)
      ok3 = Eq.and.right(Str.clear(k, '"'), Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')),
        Eq.and.right(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
          Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))), ok))
      Str.and_true(Str.clear(pair.line(T.Kv{k, v}), '\n'), Str.clear.all(pair.lines(t), '\n'),
        Str.clear_append(T.key(k), " = " ++ T.quote(v), '\n',
          key_clear.go(k, T.bare(k), Eq.and.left(Str.clear(k, '\n'), Str.clear(v, '\n'), ok3)),
          Str.clear_append(v, "\"", '\n',
            Eq.and.right(Str.clear(k, '\n'), Str.clear(v, '\n'),
              Eq.and.right(Str.clear(k, '"'), Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')),
                Eq.and.right(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
                  Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))),
                  Eq.and.left(kv.ok(T.Kv{k, v}), kvs.ok(t), eok)))), {==})),
        pairs_clear(t, Eq.and.right(kv.ok(T.Kv{k, v}), kvs.ok(t), eok)))

# LAW: no line of a document that reads back holds a newline
law lines_clear:
  for +ss: List<&2, T.Sect>
  for +eok: {sects.ok(ss) == True{} : Bool}
  {Str.clear.all(doc.lines(ss), '\n') == True{} : Bool}

# by induction on the tables
def lines_clear(ss, eok):
  match ss:
    case []:
      {==}
    case T.Sect{+n, +ps} <> +t:
      ok = Eq.and.right(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), kvs.ok(ps)),
        Eq.and.left(sect.ok(T.Sect{n, ps}), sects.ok(t), eok))
      Str.and_true(Str.clear(head.line(n), '\n'),
        Str.clear.all(List.append(&2, String, pair.lines(ps), "" <> doc.lines(t)), '\n'),
        Str.clear_append(n, "]", '\n', Eq.and.left(Str.clear(n, '\n'), kvs.ok(ps), ok), {==}),
        Str.clear_all_append(pair.lines(ps), "" <> doc.lines(t), '\n',
          pairs_clear(ps, Eq.and.right(Str.clear(n, '\n'), kvs.ok(ps),
            Eq.and.right(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), kvs.ok(ps)),
              Eq.and.left(sect.ok(T.Sect{n, ps}), sects.ok(t), eok)))),
          lines_clear(t, Eq.and.right(sect.ok(T.Sect{n, ps}), sects.ok(t), eok))))

# LAW: parsing a rendered document gives back the tables it was rendered
# from, when every table and pair can be read back and there is at least one
law sections_read:
  for +s: T.Sect
  for +t: List<&2, T.Sect>
  for +eok: {sects.ok(s <> t) == True{} : Bool}
  {T.sects(T.parse(T.render(s <> t))) == s <> t : List<&2, T.Sect>}

# the text is the lines joined, which cut back into the lines
def sections_read(s, t, eok):
  match s:
    case T.Sect{+n, +ps}:
      r = Equal.sym(String, T.render(T.Sect{n, ps} <> t),
        String.join(doc.lines(T.Sect{n, ps} <> t), "\n"), render_lines(T.Sect{n, ps} <> t))
      %r : {T.sects(T.parse(_)) == T.Sect{n, ps} <> t : List<&2, T.Sect>}
      sp = Equal.sym(List<&2, String>,
        String.split(String.join(doc.lines(T.Sect{n, ps} <> t), "\n"), '\n'),
        doc.lines(T.Sect{n, ps} <> t),
        Str.split_join(head.line(n),
          List.append(&2, String, pair.lines(ps), "" <> doc.lines(t)), '\n',
          lines_clear(T.Sect{n, ps} <> t, eok)))
      %sp : {T.sects(T.parse.fin(T.parse.walk(_, T.Toml{"", "", [], []})))
        == T.Sect{n, ps} <> t : List<&2, T.Sect>}
      Equal.cong(T.Toml, List<&2, T.Sect>, x => T.sects(x),
        T.parse.fin(T.parse.walk(doc.lines(T.Sect{n, ps} <> t), T.Toml{"", "", [], []})),
        T.Toml{"", "", [], T.Sect{n, ps} <> t},
        walk_doc(T.Sect{n, ps} <> t, "", "", [], [], eok))

# LAW: tables one after another render as their texts one after another
law render_all_append:
  for +xs: List<&2, T.Sect>
  for +ys: List<&2, T.Sect>
  {T.render.all(List.append(&2, T.Sect, xs, ys))
    == List.append(&2, String, T.render.all(xs), T.render.all(ys)) : List<&2, String>}

# by induction on the first tables
def render_all_append(xs, ys):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, String>, List<&2, String>, r => T.render.sect(h) <> r,
        T.render.all(List.append(&2, T.Sect, t, ys)),
        List.append(&2, String, T.render.all(t), T.render.all(ys)),
        render_all_append(t, ys))

# LAW: two documents that read back, one after the other, read back
law sects_ok_append:
  for +xs: List<&2, T.Sect>
  for +ys: List<&2, T.Sect>
  for +ex: {sects.ok(xs) == True{} : Bool}
  for ey: {sects.ok(ys) == True{} : Bool}
  {sects.ok(List.append(&2, T.Sect, xs, ys)) == True{} : Bool}

# by induction on the first tables
def sects_ok_append(xs, ys, ex, ey):
  match xs:
    case []:
      ey
    case +h <> +t:
      Str.and_true(sect.ok(h), sects.ok(List.append(&2, T.Sect, t, ys)),
        Eq.and.left(sect.ok(h), sects.ok(t), ex),
        sects_ok_append(t, ys, Eq.and.right(sect.ok(h), sects.ok(t), ex), ey))

# LAW: the tables before a document that reads back, when the whole does
law sects_ok_left:
  for +xs: List<&2, T.Sect>
  for +ys: List<&2, T.Sect>
  for +e: {sects.ok(List.append(&2, T.Sect, xs, ys)) == True{} : Bool}
  {sects.ok(xs) == True{} : Bool}

# by induction on the first tables
def sects_ok_left(xs, ys, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Str.and_true(sect.ok(h), sects.ok(t),
        Eq.and.left(sect.ok(h), sects.ok(List.append(&2, T.Sect, t, ys)), e),
        sects_ok_left(t, ys, Eq.and.right(sect.ok(h), sects.ok(List.append(&2, T.Sect, t, ys)), e)))

# LAW: and the tables after them
law sects_ok_right:
  for +xs: List<&2, T.Sect>
  for +ys: List<&2, T.Sect>
  for +e: {sects.ok(List.append(&2, T.Sect, xs, ys)) == True{} : Bool}
  {sects.ok(ys) == True{} : Bool}

# by induction on the first tables
def sects_ok_right(xs, ys, e):
  match xs:
    case []:
      e
    case +h <> +t:
      sects_ok_right(t, ys, Eq.and.right(sect.ok(h), sects.ok(List.append(&2, T.Sect, t, ys)), e))

# ---------------------------------------------------------------------------
# a table's header, cut into segments

# LAW: a header walked in two parts is the second walked from where the
# first left off
law seg_walk_append:
  for +xs: List<&2, Char>
  for +ys: List<&2, Char>
  for +st: T.Split
  {T.seg.walk(List.append(&2, Char, xs, ys), st) == T.seg.walk(ys, T.seg.walk(xs, st))
    : T.Split}

# by induction on the first part
def seg_walk_append(xs, ys, st):
  match xs:
    case []:
      {==}
    case +h <> +t:
      seg_walk_append(t, ys, T.seg.step(st, h))

# LAW: inside quotes, a char that is no quote joins the segment, one char,
# with whether it is a dot given
law seg_quoted.step:
  for +c: Char
  for +t: List<&2, Char>
  for +cur: List<&2, Char>
  for +out: List<&2, String>
  for b: Bool
  for +eb: {Char.is_eq(c, '.') == b : Bool}
  for eq: {Char.is_eq(c, '"') == False{} : Bool}
  for ih: {T.seg.walk(t, T.Split{True{}, c <> cur, out})
    == T.Split{True{}, List.reverse.go(&2, Char, t, c <> cur), out} : T.Split}
  {T.seg.walk(t, T.seg.go(T.Split{True{}, cur, out}, T.seg.sym(c)))
    == T.Split{True{}, List.reverse.go(&2, Char, t, c <> cur), out} : T.Split}

def seg_quoted.step(c, t, cur, out, b, eb, eq, ih):
  match b:
    case True{}:
      f = Equal.sym(Bool, Char.is_eq(c, '"'), False{}, eq)
      %f : {T.seg.walk(t, T.seg.go(T.Split{True{}, cur, out},
        Bool.pick(T.Sym, _, T.SQuote{}, Bool.pick(T.Sym, Char.is_eq(c, '.'), T.SDot{}, T.SKeep{c}))))
        == T.Split{True{}, List.reverse.go(&2, Char, t, c <> cur), out} : T.Split}
      g = Equal.sym(Bool, Char.is_eq(c, '.'), True{}, eb)
      %g : {T.seg.walk(t, T.seg.go(T.Split{True{}, cur, out},
        Bool.pick(T.Sym, False{}, T.SQuote{}, Bool.pick(T.Sym, _, T.SDot{}, T.SKeep{c}))))
        == T.Split{True{}, List.reverse.go(&2, Char, t, c <> cur), out} : T.Split}
      d = Str.char_eq_true(c, '.', eb)
      %d : {T.seg.walk(t, T.Split{True{}, _ <> cur, out})
        == T.Split{True{}, List.reverse.go(&2, Char, t, c <> cur), out} : T.Split}
      ih
    case False{}:
      f = Equal.sym(Bool, Char.is_eq(c, '"'), False{}, eq)
      %f : {T.seg.walk(t, T.seg.go(T.Split{True{}, cur, out},
        Bool.pick(T.Sym, _, T.SQuote{}, Bool.pick(T.Sym, Char.is_eq(c, '.'), T.SDot{}, T.SKeep{c}))))
        == T.Split{True{}, List.reverse.go(&2, Char, t, c <> cur), out} : T.Split}
      g = Equal.sym(Bool, Char.is_eq(c, '.'), False{}, eb)
      %g : {T.seg.walk(t, T.seg.go(T.Split{True{}, cur, out},
        Bool.pick(T.Sym, False{}, T.SQuote{}, Bool.pick(T.Sym, _, T.SDot{}, T.SKeep{c}))))
        == T.Split{True{}, List.reverse.go(&2, Char, t, c <> cur), out} : T.Split}
      ih

# LAW: inside quotes, chars with no quote among them all join the segment
law seg_quoted:
  for +cs: String
  for +cur: List<&2, Char>
  for +out: List<&2, String>
  for +e: {Str.clear(cs, '"') == True{} : Bool}
  {T.seg.walk(String.to_list(cs), T.Split{True{}, cur, out})
    == T.Split{True{}, List.reverse.go(&2, Char, String.to_list(cs), cur), out} : T.Split}

# by induction on the chars
def seg_quoted(cs, cur, out, e):
  match cs:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      seg_quoted.step(c, String.to_list(t), cur, out, Char.is_eq(c, '.'), {==},
        Eq.not.true(Char.is_eq(c, '"'), Eq.and.left(Bool.not(Char.is_eq(c, '"')), Str.clear(t, '"'), e)),
        seg_quoted(t, c <> cur, out, Eq.and.right(Bool.not(Char.is_eq(c, '"')), Str.clear(t, '"'), e)))

# LAW: outside quotes, chars with no quote and no dot all join the segment
law seg_plain:
  for +cs: String
  for +cur: List<&2, Char>
  for +out: List<&2, String>
  for +eq: {Str.clear(cs, '"') == True{} : Bool}
  for +ed: {Str.clear(cs, '.') == True{} : Bool}
  {T.seg.walk(String.to_list(cs), T.Split{False{}, cur, out})
    == T.Split{False{}, List.reverse.go(&2, Char, String.to_list(cs), cur), out} : T.Split}

# by induction on the chars, each one kept
def seg_plain(cs, cur, out, eq, ed):
  match cs:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      f = Equal.sym(Bool, Char.is_eq(c, '"'), False{},
        Eq.not.true(Char.is_eq(c, '"'), Eq.and.left(Bool.not(Char.is_eq(c, '"')), Str.clear(t, '"'), eq)))
      %f : {T.seg.walk(String.to_list(t), T.seg.go(T.Split{False{}, cur, out},
        Bool.pick(T.Sym, _, T.SQuote{}, Bool.pick(T.Sym, Char.is_eq(c, '.'), T.SDot{}, T.SKeep{c}))))
        == T.Split{False{}, List.reverse.go(&2, Char, String.to_list(t), c <> cur), out} : T.Split}
      g = Equal.sym(Bool, Char.is_eq(c, '.'), False{},
        Eq.not.true(Char.is_eq(c, '.'), Eq.and.left(Bool.not(Char.is_eq(c, '.')), Str.clear(t, '.'), ed)))
      %g : {T.seg.walk(String.to_list(t), T.seg.go(T.Split{False{}, cur, out},
        Bool.pick(T.Sym, False{}, T.SQuote{}, Bool.pick(T.Sym, _, T.SDot{}, T.SKeep{c}))))
        == T.Split{False{}, List.reverse.go(&2, Char, String.to_list(t), c <> cur), out} : T.Split}
      seg_plain(t, c <> cur, out,
        Eq.and.right(Bool.not(Char.is_eq(c, '"')), Str.clear(t, '"'), eq),
        Eq.and.right(Bool.not(Char.is_eq(c, '.')), Str.clear(t, '.'), ed))

# LAW: a segment gathered in reverse, closed, is the chars it gathered
law seg_done_rev:
  for +s: String
  {T.seg.done(List.reverse.go(&2, Char, String.to_list(s), [])) == s : String}

# the chars were reversed twice
def seg_done_rev(s):
  r = Equal.sym(List<&2, Char>,
    List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(s), []), []),
    String.to_list(s),
    Equal.trans(List<&2, Char>,
      List.reverse.go(&2, Char, List.reverse.go(&2, Char, String.to_list(s), []), []),
      List.append(&2, Char, String.to_list(s), []), String.to_list(s),
      Str.rev_rev(String.to_list(s), [], []), Str.list_append_nil(Char, String.to_list(s))))
  %r : {String.from_list(_) == s : String}
  Str.from_to(s)

# a header cut with some segments already behind it. Proof vocabulary.
def seg.frame(st: T.Split, out: List<&2, String>) -> T.Split:
  T.Split{q, cur, o} = st
  T.Split{q, cur, List.append(&2, String, o, out)}

# LAW: a dot, with segments already behind it
law dot_frame:
  for q: Bool
  for +cur: List<&2, Char>
  for +o: List<&2, String>
  for +out: List<&2, String>
  {T.seg.dot(q, cur, List.append(&2, String, o, out)) == seg.frame(T.seg.dot(q, cur, o), out)
    : T.Split}

# inside quotes and out
def dot_frame(q, _cur, _o, _out):
  match q:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: one char, with segments already behind it
law go_frame:
  for +q: Bool
  for +cur: List<&2, Char>
  for +o: List<&2, String>
  for +out: List<&2, String>
  for s: T.Sym
  {T.seg.go(T.Split{q, cur, List.append(&2, String, o, out)}, s)
    == seg.frame(T.seg.go(T.Split{q, cur, o}, s), out) : T.Split}

# each kind of char
def go_frame(q, cur, o, out, s):
  match s:
    case T.SQuote{}:
      {==}
    case T.SDot{}:
      dot_frame(q, cur, o, out)
    case T.SKeep{c}:
      {==}

# LAW: one step of a walk, with segments already behind it
law step_frame:
  for +st: T.Split
  for +out: List<&2, String>
  for +c: Char
  {T.seg.step(seg.frame(st, out), c) == seg.frame(T.seg.step(st, c), out) : T.Split}

# the state taken apart
def step_frame(st, out, c):
  match st:
    case T.Split{+q, +cur, +o}:
      go_frame(q, cur, o, out, T.seg.sym(c))

# LAW: a whole walk, with segments already behind it
law walk_frame:
  for +cs: List<&2, Char>
  for +st: T.Split
  for +out: List<&2, String>
  {T.seg.walk(cs, seg.frame(st, out)) == seg.frame(T.seg.walk(cs, st), out) : T.Split}

# by induction on the chars, one step at a time
def walk_frame(cs, st, out):
  match cs:
    case []:
      {==}
    case +h <> +t:
      s = Equal.sym(T.Split, T.seg.step(seg.frame(st, out), h),
        seg.frame(T.seg.step(st, h), out), step_frame(st, out, h))
      %s : {T.seg.walk(t, _) == seg.frame(T.seg.walk(t, T.seg.step(st, h)), out) : T.Split}
      walk_frame(t, T.seg.step(st, h), out)

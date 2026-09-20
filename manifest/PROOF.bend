# manifest: the proofs. `bend PROOF.bend` is the gate.
import Base
import ./toml.bend as T
import ./manifest.bend as M
import ./render.bend as R
import ../check/eq.bend as Eq
import ./LAWS.bend as Laws

# LAW: the chars of two strings joined are the chars of each, joined
law to_list_append:
  for a: String
  for +b: String
  {String.to_list(String.append(a, b))
    == List.append(&2, Char, String.to_list(a), String.to_list(b))
    : List<&2, Char>}

def to_list_append(a, b):
  match a:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(List<&2, Char>, List<&2, Char>, y => h <> y,
        String.to_list(String.append(t, b)),
        List.append(&2, Char, String.to_list(t), String.to_list(b)),
        to_list_append(t, b))

# LAW: a string taken apart into chars and put back together is itself
law from_to:
  for +s: String
  {String.from_list(String.to_list(s)) == s : String}

def from_to(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(String, String, y => SCon{h, y},
        String.from_list(String.to_list(t)), t, from_to(t))

# LAW: the walk to the end drops the char it was told to drop, and keeps the
# one it was carrying
law back_snoc.go:
  for t: List<&2, Char>
  for +h: Char
  for +c: Char
  {T.strip.back.go(List.append(&2, Char, t, [c]), h, c) == h <> t
    : List<&2, Char>}

def back_snoc.go(t, h, c):
  match t:
    case []:
      Equal.cong(Bool, List<&2, Char>, x => h <> T.strip.cut(x, c, []),
        Char.is_eq(c, c), True{}, Eq.char_eq_self(c))
    case +h2 <> t2:
      Equal.cong(List<&2, Char>, List<&2, Char>, y => h <> y,
        T.strip.back.go(List.append(&2, Char, t2, [c]), h2, c), h2 <> t2,
        back_snoc.go(t2, h2, c))

# LAW: a char put on the end of a list is the char the back strip takes off
law back_snoc:
  for cs: List<&2, Char>
  for +c: Char
  {T.strip.back(List.append(&2, Char, cs, [c]), c) == cs : List<&2, Char>}

def back_snoc(cs, c):
  match cs:
    case []:
      Equal.cong(Bool, List<&2, Char>, x => T.strip.cut(x, c, []),
        Char.is_eq(c, c), True{}, Eq.char_eq_self(c))
    case +h <> t:
      back_snoc.go(t, h, c)

def Laws.quote_strip(s):
  Equal.trans(String,
    T.strip(T.quote(s), '"', '"'),
    String.from_list(String.to_list(s)),
    s,
    Equal.trans(String,
      T.strip(T.quote(s), '"', '"'),
      String.from_list(T.strip.back(
        List.append(&2, Char, String.to_list(s), ['"']), '"')),
      String.from_list(String.to_list(s)),
      Equal.cong(List<&2, Char>, String,
        y => String.from_list(T.strip.back(y, '"')),
        String.to_list(String.append(s, "\"")),
        List.append(&2, Char, String.to_list(s), ['"']),
        to_list_append(s, "\"")),
      Equal.cong(List<&2, Char>, String, y => String.from_list(y),
        T.strip.back(List.append(&2, Char, String.to_list(s), ['"']), '"'),
        String.to_list(s),
        back_snoc(String.to_list(s), '"'))),
    from_to(s))

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

# The two agreement laws at the foot of LAWS.bend, which say that this pass's
# rewrites for cost did not change an answer. Each is the same argument: a
# `match` may not scrutinise a computed value, so the branch is lifted into a
# parameter and the law is then applied to the branch the code computes. The
# classifier takes four of them, one a level, in the order the cascade asks
# its questions.

# LAW: the last question, with the branch given as a parameter
law line_of_agrees.pair:
  for +s: String
  for p: Bool
  {Bool.pick(T.Line, p, T.pair_of(String.split(s, '=')),
    T.LBad{s ++ " is neither a section header nor a key"})
    == T.line_of.pair(p, s) : T.Line}

def line_of_agrees.pair(_s, p):
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: the section header, with the pair question's agreement alongside
law line_of_agrees.head:
  for +s: String
  for p: Bool
  for ih: {Bool.pick(T.Line, String.contains(s, "="),
    T.pair_of(String.split(s, '=')),
    T.LBad{s ++ " is neither a section header nor a key"})
    == T.line_of.pair(String.contains(s, "="), s) : T.Line}
  {Bool.pick(T.Line, p, T.head_of(s, String.ends_with(s, "]")),
    Bool.pick(T.Line, String.contains(s, "="),
      T.pair_of(String.split(s, '=')),
      T.LBad{s ++ " is neither a section header nor a key"}))
    == T.line_of.head(p, s) : T.Line}

def line_of_agrees.head(_s, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: the comment, with the header question's agreement alongside
law line_of_agrees.comment:
  for +s: String
  for p: Bool
  for ih: {Bool.pick(T.Line, String.starts_with(s, "["),
    T.head_of(s, String.ends_with(s, "]")),
    Bool.pick(T.Line, String.contains(s, "="),
      T.pair_of(String.split(s, '=')),
      T.LBad{s ++ " is neither a section header nor a key"}))
    == T.line_of.head(String.starts_with(s, "["), s) : T.Line}
  {Bool.pick(T.Line, p, T.LSkip{},
    Bool.pick(T.Line, String.starts_with(s, "["),
      T.head_of(s, String.ends_with(s, "]")),
      Bool.pick(T.Line, String.contains(s, "="),
        T.pair_of(String.split(s, '=')),
        T.LBad{s ++ " is neither a section header nor a key"})))
    == T.line_of.comment(p, s) : T.Line}

def line_of_agrees.comment(_s, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

# LAW: the blank line, with the comment question's agreement alongside. This
# is the arm that matters most: a cascade without it would fall through to
# calling an empty line neither a header nor a key.
law line_of_agrees.blank:
  for +s: String
  for p: Bool
  for ih: {Bool.pick(T.Line, String.starts_with(s, "#"), T.LSkip{},
    Bool.pick(T.Line, String.starts_with(s, "["),
      T.head_of(s, String.ends_with(s, "]")),
      Bool.pick(T.Line, String.contains(s, "="),
        T.pair_of(String.split(s, '=')),
        T.LBad{s ++ " is neither a section header nor a key"})))
    == T.line_of.comment(String.starts_with(s, "#"), s) : T.Line}
  {Bool.pick(T.Line, p, T.LSkip{},
    Bool.pick(T.Line, String.starts_with(s, "#"), T.LSkip{},
      Bool.pick(T.Line, String.starts_with(s, "["),
        T.head_of(s, String.ends_with(s, "]")),
        Bool.pick(T.Line, String.contains(s, "="),
          T.pair_of(String.split(s, '=')),
          T.LBad{s ++ " is neither a section header nor a key"}))))
    == T.line_of.blank(p, s) : T.Line}

def line_of_agrees.blank(_s, p, ih):
  match p:
    case True{}:
      {==}
    case False{}:
      ih

def Laws.line_of_agrees(s):
  line_of_agrees.blank(s, String.is_empty(s),
    line_of_agrees.comment(s, String.starts_with(s, "#"),
      line_of_agrees.head(s, String.starts_with(s, "["),
        line_of_agrees.pair(s, String.contains(s, "=")))))

# LAW: one step of the bare-key walk, with the head's answer given as a
# parameter and the rest of the walk's agreement alongside
law bare_all_agrees.arm:
  for t: List<&2, Char>
  for p: Bool
  for ih: {Laws.old.bare.all(t) == T.bare.all(t) : Bool}
  {Bool.and(p, Laws.old.bare.all(t))
    == T.bare.all.step(p, _u => T.bare.all(t)) : Bool}

def bare_all_agrees.arm(_t, p, ih):
  match p:
    case True{}:
      ih
    case False{}:
      {==}

def Laws.bare_all_agrees(cs):
  match cs:
    case []:
      {==}
    case +h <> +t:
      bare_all_agrees.arm(t, T.bare.at(h), Laws.bare_all_agrees(t))

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

# The rest of the ledger begins here. Most of these laws are a hypothesis
# rewritten into the one place the code branches, or a destructure the law
# states and the proof has to reach by matching, since a `match` may not
# scrutinise a computed value. The boolean facts they end on are in
# check/eq.bend.

# LAW: a list reversed onto something is never empty
law reverse_onto_nonempty:
  for ys: List<&2, String>
  for x: String
  for xs: List<&2, String>
  {List.is_empty(&2, String, List.reverse.go(&2, String, ys, x <> xs))
    == False{} : Bool}

def reverse_onto_nonempty(ys, x, xs):
  match ys:
    case []:
      {==}
    case +y <> +t:
      reverse_onto_nonempty(t, y, x <> xs)

# LAW: nothing taken off the front of a string leaves the string
law drop_zero:
  for s: String
  {String.drop(s, 0n) == s : String}

def drop_zero(s):
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

# A leading space is dropped by the first pass and never reaches the second,
# so both passes compute down to the passes over the rest of the line.
def Laws.trim_drops_leading_space(_s):
  {==}

def Laws.first_error_wins(bad, why, e):
  %e : {Bool.pick(String, _, why, bad) == bad : String}
  {==}

def Laws.flush_skips_unnamed(_pairs, _done):
  {==}

def Laws.flush_keeps_named(name, pairs, done, e):
  %e : {T.flush.put(_, name, pairs, done)
    == T.Sect{name, List.reverse(&2, T.Kv, pairs)} <> done : List<&2, T.Sect>}
  {==}

def Laws.put_outside_section_is_bad(_bad, _pairs, _done, _key, _val):
  {==}

def Laws.put_in_section(bad, name, pairs, done, key, val, e):
  %e : {T.put.go(_, bad, name, pairs, done, key, val)
    == T.Toml{bad, name, T.Kv{key, val} <> pairs, done} : T.Toml}
  {==}

# A blank line trims to a blank line, which `line_of` answers on its first
# question; the state is then handed back field for field, which is the state
# only once it is matched.
def Laws.step_skips_blank(st):
  match st:
    case T.Toml{bad, name, pairs, done}:
      {==}

# LAW: a line that opens with `#` is a skip, whatever it holds. An empty
# line is a skip too, so the emptiness question does not matter here.
law line_of_comment:
  for +s: String
  for e: {True{} == String.starts_with(s, "#") : Bool}
  {T.line_of(s) == T.LSkip{} : T.Line}

# LAW: the same, with the emptiness question given as a parameter
law line_of_comment.at:
  for +s: String
  for empty: Bool
  for e: {True{} == String.starts_with(s, "#") : Bool}
  {T.line_of.blank(empty, s) == T.LSkip{} : T.Line}

def line_of_comment.at(s, empty, e):
  match empty:
    case True{}:
      {==}
    case False{}:
      Equal.trans(T.Line,
        T.line_of.comment(String.starts_with(s, "#"), s),
        T.line_of.comment(True{}, s),
        T.LSkip{},
        Equal.cong(Bool, T.Line, b => T.line_of.comment(b, s),
          String.starts_with(s, "#"), True{},
          Equal.sym(Bool, True{}, String.starts_with(s, "#"), e)),
        {==})

def line_of_comment(s, e):
  line_of_comment.at(s, String.is_empty(s), e)

# A comment trims to a comment; the classifier skips it and the state
# comes back field for field, the way a blank line does.
def Laws.step_skips_comment(st, s, e):
  match st:
    case T.Toml{bad, name, pairs, done}:
      Equal.cong(T.Line, T.Toml, line => T.step.go(T.Toml{bad, name, pairs, done}, line),
        T.line_of(T.trim(s)), T.LSkip{}, line_of_comment(T.trim(s), e))

def Laws.unclosed_header(s, e):
  %e : {T.head_of(s, _) == T.LBad{s ++ " is not a section header"} : T.Line}
  {==}

# LAW: whatever a walk left open, the flush at the end closes
law parse_closes_sections.fin:
  for r: T.Toml
  {Laws.toml.open(T.parse.fin(r)) == "" : String}

def parse_closes_sections.fin(r):
  match r:
    case T.Toml{bad, name, pairs, done}:
      {==}

def Laws.parse_closes_sections(text):
  parse_closes_sections.fin(
    T.parse.walk(String.lines(text), T.Toml{"", "", [], []}))

def Laws.sects_is_done(_bad, _name, _pairs, _done):
  {==}

# LAW: a finished header walk always has a segment to close
law segments_never_empty.fin:
  for st: T.Split
  {List.is_empty(&2, String, T.seg.fin(st)) == False{} : Bool}

def segments_never_empty.fin(st):
  match st:
    case T.Split{quoted, cur, out}:
      reverse_onto_nonempty(out, T.seg.done(cur), [])

def Laws.segments_never_empty(s):
  segments_never_empty.fin(
    T.seg.walk(String.to_list(s), T.Split{False{}, [], []}))

# A quote is answered by `seg.sym` on the character alone, and the two
# togglings cancel before the rest of the header is read.
def Laws.segments_quotes_toggle(_s):
  {==}

# A quote, a dot, a quote: the quotes toggle and the dot is kept, so the
# rest of the header is read with that one character already gathered.
def Laws.segments_quoted_dot(_s):
  {==}

def Laws.bare_needs_a_char(s, e):
  %e : {Bool.and(Bool.not(_), T.bare.all(String.to_list(s))) == False{}
    : Bool}
  {==}

def Laws.key_is_bare_when_it_can(s, e):
  %e : {Bool.pick(String, _, s, T.quote(s)) == s : String}
  {==}

def Laws.key_is_quoted_when_it_must(s, e):
  %e : {Bool.pick(String, _, s, T.quote(s)) == T.quote(s) : String}
  {==}

# One table is joined with nothing after it, so the separator is never
# written.
def Laws.render_one_table(_n, _ps):
  {==}

# The ledger's lookup is the table's, and the table answers a key it just
# wrote.
def Laws.value_first_in_section(k, v, ps):
  Equal.cong(Bool, String, b => Bool.pick(String, b, v, T.value(ps, k)),
    String.eq(k, k), True{}, Eq.string_eq_self(k))

def Laws.pairs_of_first(name, ps, ss):
  Equal.cong(Bool, List<&2, T.Kv>,
    b => Bool.pick(List<&2, T.Kv>, b, ps, M.pairs_of(ss, name)),
    String.eq(name, name), True{}, Eq.string_eq_self(name))

def Laws.source_of_hub(pairs, e):
  %e : {M.source.go(_, M.value(pairs, "git"), M.value(pairs, "rev"),
    M.value(pairs, "tag"), M.root.or(M.value(pairs, "root")),
    M.value(pairs, "narHash")) == M.Hub{} : M.Source}
  {==}

def Laws.source_of_absent_root(pairs, e0, e1):
  %e1 : {M.source.go(String.is_empty(M.value(pairs, "git")),
    M.value(pairs, "git"), M.value(pairs, "rev"),
    M.value(pairs, "tag"), Bool.pick(String, _, ".", M.value(pairs, "root")),
    M.value(pairs, "narHash"))
    == M.Git{M.value(pairs, "git"), M.value(pairs, "rev"),
      M.value(pairs, "tag"), ".", M.value(pairs, "narHash")} : M.Source}
  %e0 : {M.source.go(_, M.value(pairs, "git"), M.value(pairs, "rev"),
    M.value(pairs, "tag"), ".", M.value(pairs, "narHash"))
    == M.Git{M.value(pairs, "git"), M.value(pairs, "rev"),
      M.value(pairs, "tag"), ".", M.value(pairs, "narHash")} : M.Source}
  {==}

# `deps.` is five literal characters, so the drop steps through all five and
# what is left is the name with nothing taken off it.
def Laws.dep_of_drops_prefix(name, _pairs):
  drop_zero(name)

def Laws.name_of_sect(_n, _ps):
  {==}

# The section's name opens with the prefix because it was built from it.
def Laws.deps_takes_dep_sections(name, ps, ss):
  Equal.cong(Bool, List<&2, M.Dep>,
    b => M.deps.put(b, T.Sect{String.append("deps.", name), ps}, M.deps(ss)),
    String.starts_with(String.append("deps.", name), "deps."), True{},
    Eq.starts_append("deps.", name))

def Laws.deps_skips_other_sections(n, ps, ss, e):
  %e : {M.deps.put(_, T.Sect{n, ps}, M.deps(ss)) == M.deps(ss)
    : List<&2, M.Dep>}
  {==}

def Laws.missing_finds_first(n, ps, ss, e0, e1):
  %e0 : {M.missing.at(Bool.and(_, String.is_empty(M.value(ps, "hash"))), n,
    M.missing(ss)) == n : String}
  %e1 : {M.missing.at(Bool.and(True{}, _), n, M.missing(ss)) == n : String}
  {==}

def Laws.problem_syntax_first(bad, miss, e):
  %e : {Bool.pick(String, _,
    Bool.pick(String, String.is_empty(miss), "", miss ++ " has no hash"), bad)
    == bad : String}
  {==}

def Laws.build_is_good(_ss):
  {==}

def Laws.read_refuses_a_problem(bad, ss, e):
  %e : {M.read.go(_, M.problem(bad, M.missing(ss)), ss)
    == M.Bad{M.problem(bad, M.missing(ss))} : M.Read}
  {==}

def Laws.parse_reads_the_sections(_text, _bad, _name, _pairs, sects, e):
  %e : {M.parse.go(_) == M.read(_bad, sects) : M.Read}
  {==}

# `error: ` is a literal, so the comparison computes down to the reason
# against the empty prefix; a name is not, so it is the append law.
def Laws.show_bad_is_marked(why):
  Eq.starts_nil(why)

def Laws.show_good_opens_with_name(n, e, ds):
  Eq.starts_append(n,
    " " ++ e ++ " " ++ String.join(M.show.deps(ds), " "))

def Laws.find_first(n, h, en, s, t):
  Equal.cong(Bool, M.Dep,
    b => M.find.pick(b, M.Dep{n, h, en, s}, M.find(t, n)),
    String.eq(n, n), True{}, Eq.string_eq_self(n))

def Laws.dep_of_unread_is_blank(_why, _name):
  {==}

def Laws.rev_of_names_the_commit(_mn, _me, n, h, en, url, rev, tag, root, nar, t):
  Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)),
    M.find(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar}} <> t, n),
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar}},
    Laws.find_first(n, h, en, M.Git{url, rev, tag, root, nar}, t))

def Laws.tag_of_names_the_tag(_mn, _me, n, h, en, url, rev, tag, root, nar, t):
  Equal.cong(M.Dep, String, d => M.source.tag(M.source.dep(d)),
    M.find(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar}} <> t, n),
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar}},
    Laws.find_first(n, h, en, M.Git{url, rev, tag, root, nar}, t))

def Laws.line_absent(_key):
  {==}

# The tag's line is the empty string, and nothing appended in front of a run
# of appends changes the run.
def Laws.source_omits_absent_tag(_url, _rev, _root, _nar):
  {==}

def Laws.dep_opens_its_section(n, h, e, s):
  Eq.starts_append(n, "]\n" ++ R.line("hash", h) ++ R.source(s) ++ R.line("entry", e))

# By induction on the first list, with the associativity of append carrying
# each step.
def Laws.deps_splits(as, bs):
  match as:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(String,
        String.append(R.dep(h), R.deps(List.append(&2, M.Dep, t, bs))),
        String.append(R.dep(h), String.append(R.deps(t), R.deps(bs))),
        String.append(String.append(R.dep(h), R.deps(t)), R.deps(bs)),
        Equal.cong(String, String, x => String.append(R.dep(h), x),
          R.deps(List.append(&2, M.Dep, t, bs)),
          String.append(R.deps(t), R.deps(bs)), Laws.deps_splits(t, bs)),
        Equal.sym(String,
          String.append(String.append(R.dep(h), R.deps(t)), R.deps(bs)),
          String.append(R.dep(h), String.append(R.deps(t), R.deps(bs))),
          Eq.append_assoc(R.dep(h), R.deps(t), R.deps(bs))))

def Laws.show_opens_with_package(n, e, ds):
  Eq.starts_nil(R.line("name", n) ++ R.line("entry", e) ++ R.deps(ds))

def Laws.render_of_unread_is_blank(_why):
  {==}

# Removing twice is the inner list dropped twice, which is `without_idem`.
def Laws.remove_idem(m, name):
  match m:
    case M.Manifest{n, e, ds}:
      Equal.cong(List<&2, M.Dep>, M.Manifest,
        xs => M.Manifest{n, e, xs},
        R.without(R.without(ds, name), name), R.without(ds, name),
        Laws.without_idem(ds, name))

# Both sides are a known ledger, so they reduce to the same file and the
# proof is the computation itself.
def Laws.render_parse_roundtrip():
  {==}

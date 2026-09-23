# manifest: the proofs. `bend PROOF.bend` is the gate.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./manifest.bend as M
import ./render.bend as R
import ./ignore.bend as I
import ../check/eq.bend as Eq
import ../check/str.bend as Str
import ./LAWS.bend as Laws

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
    case M.Manifest{+n, +e, +b, +hb, +ds, +ts}:
      Equal.cong(List<&2, M.Dep>, M.Manifest,
        y => M.Manifest{n, e, b, hb, List.append(&2, M.Dep, y, [d]), ts},
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
    M.value(pairs, "narHash"), M.flag(M.value(pairs, "vendor")))
    == M.Hub{} : M.Source}
  {==}

def Laws.source_of_absent_root(pairs, e0, e1):
  %e1 : {M.source.go(String.is_empty(M.value(pairs, "git")),
    M.value(pairs, "git"), M.value(pairs, "rev"),
    M.value(pairs, "tag"), Bool.pick(String, _, ".", M.value(pairs, "root")),
    M.value(pairs, "narHash"), M.flag(M.value(pairs, "vendor")))
    == M.Git{M.value(pairs, "git"), M.value(pairs, "rev"),
      M.value(pairs, "tag"), ".", M.value(pairs, "narHash"),
      M.flag(M.value(pairs, "vendor"))} : M.Source}
  %e0 : {M.source.go(_, M.value(pairs, "git"), M.value(pairs, "rev"),
    M.value(pairs, "tag"), ".", M.value(pairs, "narHash"),
    M.flag(M.value(pairs, "vendor")))
    == M.Git{M.value(pairs, "git"), M.value(pairs, "rev"),
      M.value(pairs, "tag"), ".", M.value(pairs, "narHash"),
      M.flag(M.value(pairs, "vendor"))} : M.Source}
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

def Laws.tool_of_drops_prefix(name, _pairs):
  drop_zero(name)

def Laws.tools_takes_tool_sections(name, ps, ss):
  Equal.cong(Bool, List<&2, M.Tool>,
    b => M.tools.put(b, T.Sect{String.append("tools.", name), ps}, M.tools(ss)),
    String.starts_with(String.append("tools.", name), "tools."), True{},
    Eq.starts_append("tools.", name))

def Laws.tools_skips_other_sections(n, ps, ss, e):
  %e : {M.tools.put(_, T.Sect{n, ps}, M.tools(ss)) == M.tools(ss)
    : List<&2, M.Tool>}
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

def Laws.show_good_opens_with_name(n, e, _b, _hb, ds, _ts):
  Eq.starts_append(n,
    " " ++ e ++ " " ++ String.join(M.show.deps(ds), " "))

def Laws.find_first(n, h, en, s, t):
  Equal.cong(Bool, M.Dep,
    b => M.find.pick(b, M.Dep{n, h, en, s}, M.find(t, n)),
    String.eq(n, n), True{}, Eq.string_eq_self(n))

def Laws.dep_of_unread_is_blank(_why, _name):
  {==}

def Laws.rev_of_names_the_commit(_mn, _me, _mb, _mh, n, h, en, url, rev, tag, root, nar, vend, t, _ts):
  Equal.cong(M.Dep, String, d => M.source.rev(M.source.dep(d)),
    M.find(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, n),
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}},
    Laws.find_first(n, h, en, M.Git{url, rev, tag, root, nar, vend}, t))

def Laws.tag_of_names_the_tag(_mn, _me, _mb, _mh, n, h, en, url, rev, tag, root, nar, vend, t, _ts):
  Equal.cong(M.Dep, String, d => M.source.tag(M.source.dep(d)),
    M.find(M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} <> t, n),
    M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}},
    Laws.find_first(n, h, en, M.Git{url, rev, tag, root, nar, vend}, t))

def Laws.line_absent(_key):
  {==}

# The tag's line is the empty string, and nothing appended in front of a run
# of appends changes the run.
def Laws.source_omits_absent_tag(_url, _rev, _root, _nar):
  {==}

def Laws.dep_opens_its_section(n, h, e, s):
  Eq.starts_append(n, "]\n" ++ R.line("hash", h) ++ R.source(s) ++ R.line("entry", e))

def Laws.tool_opens_its_section(n, e, b, s):
  Eq.starts_append(n, "]\n" ++ R.source(s) ++ R.line("entry", e) ++ R.line("bin", b))

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

def Laws.show_opens_with_package(n, e, b, hb, ds, ts):
  Eq.starts_nil(R.line("name", n) ++ R.line("entry", e) ++ R.line("bin", b) ++
    R.line("hub", hb) ++ R.deps(ds) ++ R.tools(ts))

def Laws.render_of_unread_is_blank(_why):
  {==}

# The two defaults reduce. A named hub is the pick's other arm once its
# emptiness test is rewritten to the False the premise gives.
def Laws.hub_of_unread_is_bends(_why):
  {==}

def Laws.hub_of_absent_is_bends(_n, _e, _b, _ds, _ts):
  {==}

def Laws.hub_of_names_the_hub(_n, _e, _b, hb, _ds, _ts, f):
  %f : {Bool.pick(String, _, "https://hub.bend-lang.com", hb) == hb : String}
  {==}

# Removing twice is the inner list dropped twice, which is `without_idem`.
def Laws.remove_idem(m, name):
  match m:
    case M.Manifest{n, e, b, hb, ds, ts}:
      Equal.cong(List<&2, M.Dep>, M.Manifest,
        xs => M.Manifest{n, e, b, hb, xs, ts},
        R.without(R.without(ds, name), name), R.without(ds, name),
        Laws.without_idem(ds, name))

# The `git` key is there, so the source is a git one, and its bit is the
# `vendor` key read by `flag`.
def Laws.source_of_vendor(pairs, e):
  %e : {M.source.vendor(M.source.go(_, M.value(pairs, "git"),
    M.value(pairs, "rev"), M.value(pairs, "tag"),
    M.root.or(M.value(pairs, "root")), M.value(pairs, "narHash"),
    M.flag(M.value(pairs, "vendor")))) == M.flag(M.value(pairs, "vendor"))
    : Bool}
  {==}

# The ledger's bit is true, so the source is marked vendored, and a git
# source marked vendored says so.
def Laws.readd_keeps_vendor(ds, n, h, en, url, rev, tag, root, nar, v, e):
  %Equal.sym(Bool, M.source.vendor(M.source.dep(M.find(ds, n))), True{}, e)
    : {M.source.vendor(M.source.dep(M.Dep{n, h, en,
      R.revend(_, M.Git{url, rev, tag, root, nar, v})})) == True{} : Bool}
  {==}

# The allowlist. Both laws are proved the same way: the walk is taken apart
# one line at a time, each line's kind is lifted into a parameter so the
# walk can reduce on it, and what the walk puts in a line's place is shown
# to add nothing to the side being counted. `hashes` counts the allowlist,
# `others` the project's lines.

# LAW: nothing appended to a list of lines leaves it
law lines_app_nil:
  for xs: List<&2, String>
  {List.append(&2, String, xs, []) == xs : List<&2, String>}

def lines_app_nil(xs):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        List.append(&2, String, t, []), t, lines_app_nil(t))

# LAW: a line's hash goes in front whatever follows it
law hashes_put_app:
  for k: I.Rule
  for a: List<&2, String>
  for b: List<&2, String>
  {I.hashes.put(k, List.append(&2, String, a, b))
    == List.append(&2, String, I.hashes.put(k, a), b) : List<&2, String>}

def hashes_put_app(k, _a, _b):
  match k:
    case I.Other{}:
      {==}
    case I.Dir{}:
      {==}
    case I.Star{}:
      {==}
    case I.Lib{}:
      {==}
    case I.Pkgs{}:
      {==}
    case I.Allow{x}:
      {==}

# LAW: the allowlist of two runs of lines is the one's then the other's
law hashes_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {I.hashes(List.append(&2, String, xs, ys))
    == List.append(&2, String, I.hashes(xs), I.hashes(ys)) : List<&2, String>}

def hashes_app(xs, ys):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(List.append(&2, String, t, ys))),
        I.hashes.put(I.kind(h),
          List.append(&2, String, I.hashes(t), I.hashes(ys))),
        List.append(&2, String, I.hashes.put(I.kind(h), I.hashes(t)),
          I.hashes(ys)),
        Equal.cong(List<&2, String>, List<&2, String>,
          y => I.hashes.put(I.kind(h), y),
          I.hashes(List.append(&2, String, t, ys)),
          List.append(&2, String, I.hashes(t), I.hashes(ys)),
          hashes_app(t, ys)),
        hashes_put_app(I.kind(h), I.hashes(t), I.hashes(ys)))

# LAW: a line the project wrote goes in front whatever follows it
law others_put_app:
  for k: I.Rule
  for +line: String
  for a: List<&2, String>
  for b: List<&2, String>
  {I.others.put(k, line, List.append(&2, String, a, b))
    == List.append(&2, String, I.others.put(k, line, a), b) : List<&2, String>}

def others_put_app(k, _line, _a, _b):
  match k:
    case I.Other{}:
      {==}
    case I.Dir{}:
      {==}
    case I.Star{}:
      {==}
    case I.Lib{}:
      {==}
    case I.Pkgs{}:
      {==}
    case I.Allow{x}:
      {==}

# LAW: the project's lines of two runs are the one's then the other's
law others_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {I.others(List.append(&2, String, xs, ys))
    == List.append(&2, String, I.others(xs), I.others(ys)) : List<&2, String>}

def others_app(xs, ys):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        I.others.put(I.kind(h), h, I.others(List.append(&2, String, t, ys))),
        I.others.put(I.kind(h), h,
          List.append(&2, String, I.others(t), I.others(ys))),
        List.append(&2, String, I.others.put(I.kind(h), h, I.others(t)),
          I.others(ys)),
        Equal.cong(List<&2, String>, List<&2, String>,
          y => I.others.put(I.kind(h), h, y),
          I.others(List.append(&2, String, t, ys)),
          List.append(&2, String, I.others(t), I.others(ys)),
          others_app(t, ys)),
        others_put_app(I.kind(h), h, I.others(t), I.others(ys)))

# LAW: the line ez writes for a hash reads back as that hash's allowlist
# line. An empty hash would read back as the library directory, which is
# why neither `vended` nor `allows` ever takes one.
law kind_allow:
  for +x: String
  for e: {String.is_empty(x) == False{} : Bool}
  {I.kind(I.allow(x)) == I.Allow{x} : I.Rule}

def kind_allow(x, e):
  match x:
    case SNil{}:
      Eq.bit.absurd2(&2, {I.kind(I.allow(SNil{})) == I.Allow{SNil{}} : I.Rule}, e)
    case SCon{c, t}:
      {==}

# whether every hash of a list names something. Law vocabulary: ez never
# calls it.
def full.all(hs: List<&2, String>) -> Bool:
  match hs:
    case []:
      True{}
    case h <> t:
      +rest = full.all(t)
      Bool.and(Bool.not(String.is_empty(h)), rest)

# LAW: the left half of an `or` that answered False
law or_left:
  for a: Bool
  for b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {a == False{} : Bool}

def or_left(a, _b, e):
  match a:
    case True{}:
      Eq.bit.absurd2(&2, {True{} == False{} : Bool}, e)
    case False{}:
      {==}

# LAW: and its right half
law or_right:
  for a: Bool
  for b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_right(a, b, e):
  match a:
    case True{}:
      Eq.bit.absurd2(&2, {b == False{} : Bool}, e)
    case False{}:
      e

# LAW: a hash of a list whose hashes all name something is not empty
law full_head:
  for +h: String
  for t: List<&2, String>
  for e: {full.all(h <> t) == True{} : Bool}
  {String.is_empty(h) == False{} : Bool}

def full_head(h, t, e):
  Eq.not.true(String.is_empty(h),
    Eq.and.left(Bool.not(String.is_empty(h)), full.all(t), e))

# LAW: and neither is any hash after it
law full_tail:
  for +h: String
  for t: List<&2, String>
  for e: {full.all(h <> t) == True{} : Bool}
  {full.all(t) == True{} : Bool}

def full_tail(h, t, e):
  Eq.and.right(Bool.not(String.is_empty(h)), full.all(t), e)

# LAW: the lines ez writes for hashes that name something name exactly those
# hashes, in order
law hashes_each:
  for +hs: List<&2, String>
  for +e: {full.all(hs) == True{} : Bool}
  {I.hashes(I.allow.each(hs)) == hs : List<&2, String>}

def hashes_each(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(I.allow(h)), I.hashes(I.allow.each(t))),
        I.hashes.put(I.Allow{h}, I.hashes(I.allow.each(t))),
        h <> t,
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.allow.each(t))),
          I.kind(I.allow(h)), I.Allow{h}, kind_allow(h, full_head(h, t, e))),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.hashes(I.allow.each(t)), t, hashes_each(t, full_tail(h, t, e))))

# LAW: and none of them is the project's
law others_each:
  for +hs: List<&2, String>
  for +e: {full.all(hs) == True{} : Bool}
  {I.others(I.allow.each(hs)) == [] : List<&2, String>}

def others_each(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        I.others.put(I.kind(I.allow(h)), I.allow(h), I.others(I.allow.each(t))),
        I.others.put(I.Allow{h}, I.allow(h), I.others(I.allow.each(t))),
        [],
        Equal.cong(I.Rule, List<&2, String>,
          r => I.others.put(r, I.allow(h), I.others(I.allow.each(t))),
          I.kind(I.allow(h)), I.Allow{h}, kind_allow(h, full_head(h, t, e))),
        others_each(t, full_tail(h, t, e)))

# LAW: one hash of the walk that keeps each once, with whether it is passed
# over given as a parameter. A kept hash is not empty.
law once_full.arm:
  for +h: String
  for t: List<&2, String>
  for +seen: List<&2, String>
  for skip: Bool
  for es: {Bool.or(String.is_empty(h), I.named(seen, h)) == skip : Bool}
  for ih: {full.all(I.once.go(t, I.once.seen(skip, h, seen))) == True{} : Bool}
  {full.all(I.once.put(skip, h, I.once.go(t, I.once.seen(skip, h, seen))))
    == True{} : Bool}

def once_full.arm(h, t, seen, skip, es, ih):
  match skip:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, String.is_empty(h), False{},
        or_left(String.is_empty(h), I.named(seen, h), es))
        : {Bool.and(Bool.not(_), full.all(I.once.go(t, h <> seen))) == True{} : Bool}
      ih

# LAW: every hash the walk keeps names something
law once_full:
  for hs: List<&2, String>
  for +seen: List<&2, String>
  {full.all(I.once.go(hs, seen)) == True{} : Bool}

def once_full(hs, seen):
  match hs:
    case []:
      {==}
    case +h <> +t:
      once_full.arm(h, t, seen, Bool.or(String.is_empty(h), I.named(seen, h)), {==},
        once_full(t, I.once.seen(Bool.or(String.is_empty(h), I.named(seen, h)), h, seen)))

# LAW: so every hash a ledger vends names something
law vended_full:
  for ds: List<&2, M.Dep>
  {full.all(I.vended(ds)) == True{} : Bool}

def vended_full(ds):
  once_full(I.vendors(ds), [])

# LAW: the three rules name no hash, whichever of them are written
law rules_name_no_hash:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {I.hashes(I.rules.go(b1, b2, b3)) == [] : List<&2, String>}

def rules_name_no_hash(b1, b2, b3):
  match b1 b2 b3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: and are ez's, not the project's
law rules_are_ez:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {I.others(I.rules.go(b1, b2, b3)) == [] : List<&2, String>}

def rules_are_ez(b1, b2, b3):
  match b1 b2 b3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: the rules, written or not, name no hash
law need_hashes:
  for s: Bool
  for +rs: List<&2, String>
  for h: {I.hashes(rs) == [] : List<&2, String>}
  {I.hashes(I.need(s, rs)) == [] : List<&2, String>}

def need_hashes(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: and add none of the project's lines
law need_others:
  for s: Bool
  for +rs: List<&2, String>
  for h: {I.others(rs) == [] : List<&2, String>}
  {I.others(I.need(s, rs)) == [] : List<&2, String>}

def need_others(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: the block names exactly the vendored hashes
law block_hashes:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, I.Line>
  {I.hashes(I.block(ds, ls)) == I.vended(ds) : List<&2, String>}

def block_hashes(ds, ls):
  Equal.trans(List<&2, String>,
    I.hashes(List.append(&2, String,
      I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
        I.rules(ls)), I.allows(ds))),
    List.append(&2, String,
      I.hashes(I.need(Bool.or(I.has(ls, I.Dir{}),
        List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
      I.hashes(I.allows(ds))),
    I.vended(ds),
    hashes_app(
      I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
        I.rules(ls)), I.allows(ds)),
    Equal.trans(List<&2, String>,
      List.append(&2, String,
        I.hashes(I.need(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
        I.hashes(I.allows(ds))),
      I.hashes(I.allows(ds)),
      I.vended(ds),
      Equal.cong(List<&2, String>, List<&2, String>,
        y => List.append(&2, String, y, I.hashes(I.allows(ds))),
        I.hashes(I.need(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
        [],
        need_hashes(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls),
          rules_name_no_hash(I.has(ls, I.Star{}), I.has(ls, I.Lib{}),
            I.has(ls, I.Pkgs{})))),
      hashes_each(I.vended(ds), vended_full(ds))))

# LAW: and none of the project's lines
law block_others:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, I.Line>
  {I.others(I.block(ds, ls)) == [] : List<&2, String>}

def block_others(ds, ls):
  Equal.trans(List<&2, String>,
    I.others(List.append(&2, String,
      I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
        I.rules(ls)), I.allows(ds))),
    List.append(&2, String,
      I.others(I.need(Bool.or(I.has(ls, I.Dir{}),
        List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
      I.others(I.allows(ds))),
    [],
    others_app(
      I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
        I.rules(ls)), I.allows(ds)),
    Equal.trans(List<&2, String>,
      List.append(&2, String,
        I.others(I.need(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
        I.others(I.allows(ds))),
      I.others(I.allows(ds)),
      [],
      Equal.cong(List<&2, String>, List<&2, String>,
        y => List.append(&2, String, y, I.others(I.allows(ds))),
        I.others(I.need(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls))),
        [],
        need_others(Bool.or(I.has(ls, I.Dir{}),
          List.is_empty(&2, String, I.vended(ds))), I.rules(ls),
          rules_are_ez(I.has(ls, I.Star{}), I.has(ls, I.Lib{}),
            I.has(ls, I.Pkgs{})))),
      others_each(I.vended(ds), vended_full(ds))))

# LAW: the block, put down or not, names what it holds or nothing
law hashes_placed:
  for +d: Bool
  for +blk: List<&2, String>
  {I.hashes(I.placed(d, blk)) == I.placed(d, I.hashes(blk)) : List<&2, String>}

def hashes_placed(d, _blk):
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: and adds none of the project's lines
law others_placed:
  for +d: Bool
  for +blk: List<&2, String>
  for +ob: {I.others(blk) == [] : List<&2, String>}
  {I.others(I.placed(d, blk)) == [] : List<&2, String>}

def others_placed(d, _blk, ob):
  match d:
    case True{}:
      {==}
    case False{}:
      ob

# LAW: one line of the walk, with its kind given as a parameter. A line of
# the project's or one of the three rules is kept and names no hash, a
# `.ez/` gives way to rules that name none, and the first allowlist line
# gives way to the block, which the rest of the walk does not put down again.
law walk_hashes.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +hf: {I.hashes(fix) == [] : List<&2, String>}
  for ihd: {I.hashes(I.walk(I.tag(t), fix, blk, d)) == I.placed(d, I.hashes(blk))
    : List<&2, String>}
  for iht: {I.hashes(I.walk(I.tag(t), fix, blk, True{})) == []
    : List<&2, String>}
  {I.hashes(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d))
    == I.placed(d, I.hashes(blk)) : List<&2, String>}

def walk_hashes.arm(k, h, t, fix, blk, d, ek, hf, ihd, iht):
  match k:
    case I.Other{}:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.hashes(I.walk(I.tag(t), fix, blk, d)),
        I.placed(d, I.hashes(blk)),
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.kind(h), I.Other{}, ek),
        ihd)
    case I.Star{}:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.hashes(I.walk(I.tag(t), fix, blk, d)),
        I.placed(d, I.hashes(blk)),
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.kind(h), I.Star{}, ek),
        ihd)
    case I.Lib{}:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.hashes(I.walk(I.tag(t), fix, blk, d)),
        I.placed(d, I.hashes(blk)),
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.kind(h), I.Lib{}, ek),
        ihd)
    case I.Pkgs{}:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(h), I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.hashes(I.walk(I.tag(t), fix, blk, d)),
        I.placed(d, I.hashes(blk)),
        Equal.cong(I.Rule, List<&2, String>,
          r => I.hashes.put(r, I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.kind(h), I.Pkgs{}, ek),
        ihd)
    case I.Dir{}:
      Equal.trans(List<&2, String>,
        I.hashes(List.append(&2, String, fix, I.walk(I.tag(t), fix, blk, d))),
        List.append(&2, String, I.hashes(fix),
          I.hashes(I.walk(I.tag(t), fix, blk, d))),
        I.placed(d, I.hashes(blk)),
        hashes_app(fix, I.walk(I.tag(t), fix, blk, d)),
        Equal.trans(List<&2, String>,
          List.append(&2, String, I.hashes(fix),
            I.hashes(I.walk(I.tag(t), fix, blk, d))),
          I.hashes(I.walk(I.tag(t), fix, blk, d)),
          I.placed(d, I.hashes(blk)),
          Equal.cong(List<&2, String>, List<&2, String>,
            y => List.append(&2, String, y,
              I.hashes(I.walk(I.tag(t), fix, blk, d))),
            I.hashes(fix), [], hf),
          ihd))
    case I.Allow{x}:
      Equal.trans(List<&2, String>,
        I.hashes(List.append(&2, String, I.placed(d, blk),
          I.walk(I.tag(t), fix, blk, True{}))),
        List.append(&2, String, I.hashes(I.placed(d, blk)),
          I.hashes(I.walk(I.tag(t), fix, blk, True{}))),
        I.placed(d, I.hashes(blk)),
        hashes_app(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{})),
        Equal.trans(List<&2, String>,
          List.append(&2, String, I.hashes(I.placed(d, blk)),
            I.hashes(I.walk(I.tag(t), fix, blk, True{}))),
          List.append(&2, String, I.hashes(I.placed(d, blk)), []),
          I.placed(d, I.hashes(blk)),
          Equal.cong(List<&2, String>, List<&2, String>,
            y => List.append(&2, String, I.hashes(I.placed(d, blk)), y),
            I.hashes(I.walk(I.tag(t), fix, blk, True{})), [], iht),
          Equal.trans(List<&2, String>,
            List.append(&2, String, I.hashes(I.placed(d, blk)), []),
            I.hashes(I.placed(d, blk)),
            I.placed(d, I.hashes(blk)),
            lines_app_nil(I.hashes(I.placed(d, blk))),
            hashes_placed(d, blk))))

# LAW: the walk's allowlist is the block, once, or nothing when the block is
# already down
law walk_hashes:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +hf: {I.hashes(fix) == [] : List<&2, String>}
  {I.hashes(I.walk(I.tag(raw), fix, blk, d)) == I.placed(d, I.hashes(blk))
    : List<&2, String>}

def walk_hashes(raw, fix, blk, d, hf):
  match raw:
    case []:
      hashes_placed(d, blk)
    case +h <> +t:
      walk_hashes.arm(I.kind(h), h, t, fix, blk, d, {==}, hf,
        walk_hashes(t, fix, blk, d, hf), walk_hashes(t, fix, blk, True{}, hf))

# LAW: one line of the walk, counted for the project's lines. A kept line
# is the line; a `.ez/` and an allowlist line are ez's, and what replaces
# them is too.
law walk_others.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +of: {I.others(fix) == [] : List<&2, String>}
  for +ob: {I.others(blk) == [] : List<&2, String>}
  for ihd: {I.others(I.walk(I.tag(t), fix, blk, d)) == I.others(t)
    : List<&2, String>}
  for iht: {I.others(I.walk(I.tag(t), fix, blk, True{})) == I.others(t)
    : List<&2, String>}
  {I.others(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d))
    == I.others.put(I.kind(h), h, I.others(t)) : List<&2, String>}

def walk_others.arm(k, h, t, fix, blk, d, ek, of, ob, ihd, iht):
  match k:
    case I.Other{}:
      Equal.cong(List<&2, String>, List<&2, String>,
        y => I.others.put(I.kind(h), h, y),
        I.others(I.walk(I.tag(t), fix, blk, d)), I.others(t), ihd)
    case I.Star{}:
      Equal.cong(List<&2, String>, List<&2, String>,
        y => I.others.put(I.kind(h), h, y),
        I.others(I.walk(I.tag(t), fix, blk, d)), I.others(t), ihd)
    case I.Lib{}:
      Equal.cong(List<&2, String>, List<&2, String>,
        y => I.others.put(I.kind(h), h, y),
        I.others(I.walk(I.tag(t), fix, blk, d)), I.others(t), ihd)
    case I.Pkgs{}:
      Equal.cong(List<&2, String>, List<&2, String>,
        y => I.others.put(I.kind(h), h, y),
        I.others(I.walk(I.tag(t), fix, blk, d)), I.others(t), ihd)
    case I.Dir{}:
      Equal.trans(List<&2, String>,
        I.others(List.append(&2, String, fix, I.walk(I.tag(t), fix, blk, d))),
        List.append(&2, String, I.others(fix),
          I.others(I.walk(I.tag(t), fix, blk, d))),
        I.others.put(I.kind(h), h, I.others(t)),
        others_app(fix, I.walk(I.tag(t), fix, blk, d)),
        Equal.trans(List<&2, String>,
          List.append(&2, String, I.others(fix),
            I.others(I.walk(I.tag(t), fix, blk, d))),
          I.others(I.walk(I.tag(t), fix, blk, d)),
          I.others.put(I.kind(h), h, I.others(t)),
          Equal.cong(List<&2, String>, List<&2, String>,
            y => List.append(&2, String, y,
              I.others(I.walk(I.tag(t), fix, blk, d))),
            I.others(fix), [], of),
          Equal.trans(List<&2, String>,
            I.others(I.walk(I.tag(t), fix, blk, d)),
            I.others(t),
            I.others.put(I.kind(h), h, I.others(t)),
            ihd,
            Equal.sym(List<&2, String>,
              I.others.put(I.kind(h), h, I.others(t)), I.others(t),
              Equal.cong(I.Rule, List<&2, String>,
                r => I.others.put(r, h, I.others(t)), I.kind(h), I.Dir{}, ek)))))
    case I.Allow{x}:
      Equal.trans(List<&2, String>,
        I.others(List.append(&2, String, I.placed(d, blk),
          I.walk(I.tag(t), fix, blk, True{}))),
        List.append(&2, String, I.others(I.placed(d, blk)),
          I.others(I.walk(I.tag(t), fix, blk, True{}))),
        I.others.put(I.kind(h), h, I.others(t)),
        others_app(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{})),
        Equal.trans(List<&2, String>,
          List.append(&2, String, I.others(I.placed(d, blk)),
            I.others(I.walk(I.tag(t), fix, blk, True{}))),
          I.others(I.walk(I.tag(t), fix, blk, True{})),
          I.others.put(I.kind(h), h, I.others(t)),
          Equal.cong(List<&2, String>, List<&2, String>,
            y => List.append(&2, String, y,
              I.others(I.walk(I.tag(t), fix, blk, True{}))),
            I.others(I.placed(d, blk)), [], others_placed(d, blk, ob)),
          Equal.trans(List<&2, String>,
            I.others(I.walk(I.tag(t), fix, blk, True{})),
            I.others(t),
            I.others.put(I.kind(h), h, I.others(t)),
            iht,
            Equal.sym(List<&2, String>,
              I.others.put(I.kind(h), h, I.others(t)), I.others(t),
              Equal.cong(I.Rule, List<&2, String>,
                r => I.others.put(r, h, I.others(t)), I.kind(h), I.Allow{x},
                ek)))))

# LAW: the walk keeps every line of the project's, in order
law walk_others:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +of: {I.others(fix) == [] : List<&2, String>}
  for +ob: {I.others(blk) == [] : List<&2, String>}
  {I.others(I.walk(I.tag(raw), fix, blk, d)) == I.others(raw)
    : List<&2, String>}

def walk_others(raw, fix, blk, d, of, ob):
  match raw:
    case []:
      others_placed(d, blk, ob)
    case +h <> +t:
      walk_others.arm(I.kind(h), h, t, fix, blk, d, {==}, of, ob,
        walk_others(t, fix, blk, d, of, ob),
        walk_others(t, fix, blk, True{}, of, ob))

# The walk puts the block down once, and the block is the ledger's hashes.
def Laws.allowlist_is_the_ledger(ds, ls):
  Equal.trans(List<&2, String>,
    I.hashes(I.walk(I.tag(ls), I.rules(I.tag(ls)), I.block(ds, I.tag(ls)),
      False{})),
    I.hashes(I.block(ds, I.tag(ls))),
    I.vended(ds),
    walk_hashes(ls, I.rules(I.tag(ls)), I.block(ds, I.tag(ls)), False{},
      rules_name_no_hash(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))),
    block_hashes(ds, I.tag(ls)))

# The walk keeps the project's lines, and what it adds is all ez's.
def Laws.allowlist_keeps_other_lines(ds, ls):
  walk_others(ls, I.rules(I.tag(ls)), I.block(ds, I.tag(ls)), False{},
    rules_are_ez(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
      I.has(I.tag(ls), I.Pkgs{})),
    block_others(ds, I.tag(ls)))

# The vendor bit read back. Each bit renders one fixed ledger, and parsing
# that text is a computation the checker runs to its end.
def Laws.vendor_reads_back(v):
  match v:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: one step of the lookup past the drop, with the branch the drop takes
# given as a parameter and the equation that put it there alongside. A
# dependency the drop kept has another name, so the lookup passes it by.
law find_last.arm:
  for +h: M.Dep
  for -r: List<&2, M.Dep>
  for +n: String
  for -x: M.Dep
  for b: Bool
  for eb: {String.eq(M.dep.name(h), n) == b : Bool}
  for ih: {M.find(List.append(&2, M.Dep, r, [x]), n) == x : M.Dep}
  {M.find(List.append(&2, M.Dep, R.without.put(b, h, r), [x]), n) == x : M.Dep}

def find_last.arm(h, r, n, x, b, eb, ih):
  match h:
    case M.Dep{+hn, hh, he, hs}:
      match b:
        case True{}:
          ih
        case False{}:
          Equal.trans(M.Dep,
            M.find.pick(String.eq(hn, n), M.Dep{hn, hh, he, hs},
              M.find(List.append(&2, M.Dep, r, [x]), n)),
            M.find(List.append(&2, M.Dep, r, [x]), n),
            x,
            Equal.cong(Bool, M.Dep,
              c => M.find.pick(c, M.Dep{hn, hh, he, hs},
                M.find(List.append(&2, M.Dep, r, [x]), n)),
              String.eq(hn, n), False{}, eb),
            ih)

# LAW: a dependency put after every other entry of its name was dropped is
# the one the lookup of that name finds
law find_last:
  for ds: List<&2, M.Dep>
  for +n: String
  for +h: String
  for +e: String
  for +s: M.Source
  {M.find(List.append(&2, M.Dep, R.without(ds, n), [M.Dep{n, h, e, s}]), n)
    == M.Dep{n, h, e, s} : M.Dep}

def find_last(ds, n, h, e, s):
  match ds:
    case []:
      Equal.cong(Bool, M.Dep,
        c => M.find.pick(c, M.Dep{n, h, e, s}, M.Dep{"", "", "", M.Hub{}}),
        String.eq(n, n), True{}, Eq.string_eq_self(n))
    case +d <> t:
      find_last.arm(d, R.without(t, n), n, M.Dep{n, h, e, s},
        String.eq(M.dep.name(d), n), {==}, find_last(t, n, h, e, s))

# LAW: keeping the bit a kept source already carries changes nothing. A
# vendored git source says it is vendored, and vendoring it again is itself;
# a hub source is never vendored.
law revend_again:
  for k: Bool
  for s: M.Source
  {R.revend(M.source.vendor(R.revend(k, s)), s) == R.revend(k, s) : M.Source}

def revend_again(k, s):
  match k:
    case True{}:
      match s:
        case M.Hub{}:
          {==}
        case M.Git{url, rev, tag, root, nar, vend}:
          {==}
    case False{}:
      match s:
        case M.Hub{}:
          {==}
        case M.Git{url, rev, tag, root, nar, vend}:
          match vend:
            case True{}:
              {==}
            case False{}:
              {==}

# LAW: a dependency added again to the list the first add made is the one the
# first add wrote: the lookup finds that entry, and its bit is kept as it is
law readd_again:
  for +ds: List<&2, M.Dep>
  for +d: M.Dep
  {R.readd(List.append(&2, M.Dep, R.without(ds, M.dep.name(R.readd(ds, d))),
    [R.readd(ds, d)]), d) == R.readd(ds, d) : M.Dep}

def readd_again(ds, d):
  match d:
    case M.Dep{+n, h, e, s}:
      Equal.cong(M.Source, M.Dep, y => M.Dep{n, h, e, y},
        R.revend(M.source.vendor(M.source.dep(M.find(List.append(&2, M.Dep,
          R.without(ds, n),
          [M.Dep{n, h, e, R.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)}]),
          n))), s),
        R.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s),
        Equal.trans(M.Source,
          R.revend(M.source.vendor(M.source.dep(M.find(List.append(&2, M.Dep,
            R.without(ds, n),
            [M.Dep{n, h, e, R.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)}]),
            n))), s),
          R.revend(M.source.vendor(R.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)), s),
          R.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s),
          Equal.cong(M.Dep, M.Source,
            y => R.revend(M.source.vendor(M.source.dep(y)), s),
            M.find(List.append(&2, M.Dep, R.without(ds, n),
              [M.Dep{n, h, e, R.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)}]),
              n),
            M.Dep{n, h, e, R.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)},
            find_last(ds, n, h, e,
              R.revend(M.source.vendor(M.source.dep(M.find(ds, n))), s))),
          revend_again(M.source.vendor(M.source.dep(M.find(ds, n))), s)))

# Adding again with the kept bit is adding the dependency the first add wrote,
# by `readd_again`, and adding that twice is adding it once, by `add_idem`.
def Laws.add_keep_idem(m, d):
  match m:
    case M.Manifest{+n, +e, +b, +hb, +ds, +ts}:
      Equal.trans(M.Manifest,
        R.add(R.add(M.Manifest{n, e, b, hb, ds, ts}, R.readd(ds, d)),
          R.readd(List.append(&2, M.Dep,
            R.without(ds, M.dep.name(R.readd(ds, d))), [R.readd(ds, d)]), d)),
        R.add(R.add(M.Manifest{n, e, b, hb, ds, ts}, R.readd(ds, d)),
          R.readd(ds, d)),
        R.add(M.Manifest{n, e, b, hb, ds, ts}, R.readd(ds, d)),
        Equal.cong(M.Dep, M.Manifest,
          y => R.add(R.add(M.Manifest{n, e, b, hb, ds, ts}, R.readd(ds, d)), y),
          R.readd(List.append(&2, M.Dep,
            R.without(ds, M.dep.name(R.readd(ds, d))), [R.readd(ds, d)]), d),
          R.readd(ds, d),
          readd_again(ds, d)),
        Laws.add_idem(M.Manifest{n, e, b, hb, ds, ts}, R.readd(ds, d)))

# The text layer of the allowlist (EZ-VEN-1). `I.sync` reads a file into its
# lines, derives the allowlist over them, and writes them back, each ending
# with a newline. A file written from lines that hold no newline reads back
# as those lines, and no line read from a file holds one, so the file `sync`
# writes reads back as the lines `I.lines` made, and the line laws above hold
# of its bytes.

# LAW: an `and` of two halves that answered True
law and_tt:
  for u: Bool
  for v: Bool
  for eu: {u == True{} : Bool}
  for ev: {v == True{} : Bool}
  {Bool.and(u, v) == True{} : Bool}

def and_tt(u, v, eu, ev):
  %Equal.sym(Bool, u, True{}, eu) : {Bool.and(_, v) == True{} : Bool}
  ev

# LAW: lines written out as a file and cut at the newline are those lines and
# the empty piece after the last newline
law file_text_split:
  for +ls: List<&2, String>
  for +e: {Str.clear.all(ls, '\n') == True{} : Bool}
  {String.split(I.file.text(ls), '\n') == List.append(&2, String, ls, [""])
    : List<&2, String>}

def file_text_split(ls, e):
  match ls:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        String.split(String.append(h, SCon{'\n', I.file.text(t)}), '\n'),
        String.append(h, SNil{}) <> String.split(I.file.text(t), '\n'),
        h <> List.append(&2, String, t, [""]),
        Str.split_front(h, SCon{'\n', I.file.text(t)}, '\n', SNil{},
          String.split(I.file.text(t), '\n'),
          Eq.and.left(Str.clear(h, '\n'), Str.clear.all(t, '\n'), e),
          Str.split_sep('\n', I.file.text(t))),
        Equal.trans(List<&2, String>,
          String.append(h, SNil{}) <> String.split(I.file.text(t), '\n'),
          h <> String.split(I.file.text(t), '\n'),
          h <> List.append(&2, String, t, [""]),
          Equal.cong(String, List<&2, String>,
            x => x <> String.split(I.file.text(t), '\n'),
            String.append(h, SNil{}), h, Str.append_nil(h)),
          Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
            String.split(I.file.text(t), '\n'), List.append(&2, String, t, [""]),
            file_text_split(t, Eq.and.right(Str.clear(h, '\n'),
              Str.clear.all(t, '\n'), e)))))

# LAW: the empty piece after the last newline is dropped, and nothing else
law unend_go_app:
  for t: List<&2, String>
  for +h: String
  {I.unend.go(List.append(&2, String, t, [""]), h) == h <> t : List<&2, String>}

def unend_go_app(t, h):
  match t:
    case []:
      {==}
    case +h2 <> +t2:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.unend.go(List.append(&2, String, t2, [""]), h2), h2 <> t2,
        unend_go_app(t2, h2))

# LAW: and so a file of lines reads back as its lines
law unend_app:
  for ls: List<&2, String>
  {I.unend(List.append(&2, String, ls, [""])) == ls : List<&2, String>}

def unend_app(ls):
  match ls:
    case []:
      {==}
    case +h <> +t:
      unend_go_app(t, h)

# LAW: lines that hold no newline, written out as a file, read back as those
# lines
law file_lines_text:
  for +ls: List<&2, String>
  for +e: {Str.clear.all(ls, '\n') == True{} : Bool}
  {I.file.lines(I.file.text(ls)) == ls : List<&2, String>}

def file_lines_text(ls, e):
  Equal.trans(List<&2, String>,
    I.unend(String.split(I.file.text(ls), '\n')),
    I.unend(List.append(&2, String, ls, [""])),
    ls,
    Equal.cong(List<&2, String>, List<&2, String>, y => I.unend(y),
      String.split(I.file.text(ls), '\n'), List.append(&2, String, ls, [""]),
      file_text_split(ls, e)),
    unend_app(ls))

# LAW: dropping the last piece when it is empty leaves no line with a newline
law unend_go_clear:
  for t: List<&2, String>
  for +h: String
  for +e: {Str.clear.all(h <> t, '\n') == True{} : Bool}
  {Str.clear.all(I.unend.go(t, h), '\n') == True{} : Bool}

def unend_go_clear(t, h, e):
  match t:
    case []:
      match h:
        case SNil{}:
          {==}
        case SCon{c, r}:
          e
    case +h2 <> +t2:
      and_tt(Str.clear(h, '\n'), Str.clear.all(I.unend.go(t2, h2), '\n'),
        Eq.and.left(Str.clear(h, '\n'), Str.clear.all(h2 <> t2, '\n'), e),
        unend_go_clear(t2, h2,
          Eq.and.right(Str.clear(h, '\n'), Str.clear.all(h2 <> t2, '\n'), e)))

# LAW: and neither does any piece that is kept
law unend_clear:
  for ps: List<&2, String>
  for +e: {Str.clear.all(ps, '\n') == True{} : Bool}
  {Str.clear.all(I.unend(ps), '\n') == True{} : Bool}

def unend_clear(ps, e):
  match ps:
    case []:
      {==}
    case +h <> +t:
      unend_go_clear(t, h, e)

# LAW: no line of a file holds a newline
law file_lines_clear:
  for +text: String
  {Str.clear.all(I.file.lines(text), '\n') == True{} : Bool}

def file_lines_clear(text):
  unend_clear(String.split(text, '\n'), Str.split_clear(text, '\n'))

# LAW: two runs of lines hold no newline exactly when neither does
law clear_all_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {Str.clear.all(List.append(&2, String, xs, ys), '\n')
    == Bool.and(Str.clear.all(xs, '\n'), Str.clear.all(ys, '\n')) : Bool}

def clear_all_app(xs, ys):
  match xs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, Str.clear.all(List.append(&2, String, t, ys), '\n'),
        Bool.and(Str.clear.all(t, '\n'), Str.clear.all(ys, '\n')),
        clear_all_app(t, ys))
        : {Bool.and(Str.clear(h, '\n'), _)
          == Bool.and(Bool.and(Str.clear(h, '\n'), Str.clear.all(t, '\n')),
            Str.clear.all(ys, '\n')) : Bool}
      Str.and_assoc(Str.clear(h, '\n'), Str.clear.all(t, '\n'),
        Str.clear.all(ys, '\n'))

# LAW: two runs of lines that hold no newline hold none together
law clear_app:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for ex: {Str.clear.all(xs, '\n') == True{} : Bool}
  for ey: {Str.clear.all(ys, '\n') == True{} : Bool}
  {Str.clear.all(List.append(&2, String, xs, ys), '\n') == True{} : Bool}

def clear_app(xs, ys, ex, ey):
  Equal.trans(Bool,
    Str.clear.all(List.append(&2, String, xs, ys), '\n'),
    Bool.and(Str.clear.all(xs, '\n'), Str.clear.all(ys, '\n')),
    True{},
    clear_all_app(xs, ys),
    and_tt(Str.clear.all(xs, '\n'), Str.clear.all(ys, '\n'), ex, ey))

# LAW: the block, put down or not, holds no newline when it holds none
law placed_clear:
  for +d: Bool
  for +blk: List<&2, String>
  for eb: {Str.clear.all(blk, '\n') == True{} : Bool}
  {Str.clear.all(I.placed(d, blk), '\n') == True{} : Bool}

def placed_clear(d, _blk, eb):
  match d:
    case True{}:
      {==}
    case False{}:
      eb

# LAW: one line of the walk, with its kind given as a parameter: what the
# walk puts in its place holds no newline
law walk_clear.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +eh: {Str.clear(h, '\n') == True{} : Bool}
  for +ef: {Str.clear.all(fix, '\n') == True{} : Bool}
  for +eb: {Str.clear.all(blk, '\n') == True{} : Bool}
  for ihd: {Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n') == True{} : Bool}
  for iht: {Str.clear.all(I.walk(I.tag(t), fix, blk, True{}), '\n') == True{} : Bool}
  {Str.clear.all(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d), '\n') == True{} : Bool}

def walk_clear.arm(k, h, t, fix, blk, d, eh, ef, eb, ihd, iht):
  match k:
    case I.Other{}:
      and_tt(Str.clear(h, '\n'), Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n'),
        eh, ihd)
    case I.Star{}:
      and_tt(Str.clear(h, '\n'), Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n'),
        eh, ihd)
    case I.Lib{}:
      and_tt(Str.clear(h, '\n'), Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n'),
        eh, ihd)
    case I.Pkgs{}:
      and_tt(Str.clear(h, '\n'), Str.clear.all(I.walk(I.tag(t), fix, blk, d), '\n'),
        eh, ihd)
    case I.Dir{}:
      clear_app(fix, I.walk(I.tag(t), fix, blk, d), ef, ihd)
    case I.Allow{x}:
      clear_app(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}),
        placed_clear(d, blk, eb), iht)

# LAW: every line the walk writes is a line of the file, a rule or the block,
# so it holds no newline when none of those does
law walk_clear:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +er: {Str.clear.all(raw, '\n') == True{} : Bool}
  for +ef: {Str.clear.all(fix, '\n') == True{} : Bool}
  for +eb: {Str.clear.all(blk, '\n') == True{} : Bool}
  {Str.clear.all(I.walk(I.tag(raw), fix, blk, d), '\n') == True{} : Bool}

def walk_clear(raw, fix, blk, d, er, ef, eb):
  match raw:
    case []:
      placed_clear(d, blk, eb)
    case +h <> +t:
      walk_clear.arm(I.kind(h), h, t, fix, blk, d,
        Eq.and.left(Str.clear(h, '\n'), Str.clear.all(t, '\n'), er), ef, eb,
        walk_clear(t, fix, blk, d,
          Eq.and.right(Str.clear(h, '\n'), Str.clear.all(t, '\n'), er), ef, eb),
        walk_clear(t, fix, blk, True{},
          Eq.and.right(Str.clear(h, '\n'), Str.clear.all(t, '\n'), er), ef, eb))

# LAW: the three rules hold no newline, whichever of them are written
law rules_clear:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {Str.clear.all(I.rules.go(b1, b2, b3), '\n') == True{} : Bool}

def rules_clear(b1, b2, b3):
  match b1 b2 b3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: the rules, written or not, hold no newline
law need_clear:
  for s: Bool
  for +rs: List<&2, String>
  for h: {Str.clear.all(rs, '\n') == True{} : Bool}
  {Str.clear.all(I.need(s, rs), '\n') == True{} : Bool}

def need_clear(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: the lines ez writes for hashes that hold no newline hold none
law each_clear:
  for +hs: List<&2, String>
  for +e: {Str.clear.all(hs, '\n') == True{} : Bool}
  {Str.clear.all(I.allow.each(hs), '\n') == True{} : Bool}

def each_clear(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      and_tt(Str.clear(I.allow(h), '\n'), Str.clear.all(I.allow.each(t), '\n'),
        Eq.and.left(Str.clear(h, '\n'), Str.clear.all(t, '\n'), e),
        each_clear(t, Eq.and.right(Str.clear(h, '\n'), Str.clear.all(t, '\n'), e)))

# LAW: the block holds no newline when no vendored hash does
law block_clear:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, I.Line>
  for +e: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {Str.clear.all(I.block(ds, ls), '\n') == True{} : Bool}

def block_clear(ds, ls, e):
  clear_app(
    I.need(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
      I.rules(ls)),
    I.allows(ds),
    need_clear(Bool.or(I.has(ls, I.Dir{}), List.is_empty(&2, String, I.vended(ds))),
      I.rules(ls),
      rules_clear(I.has(ls, I.Star{}), I.has(ls, I.Lib{}), I.has(ls, I.Pkgs{}))),
    each_clear(I.vended(ds), e))

# LAW: no line of the allowlist `I.lines` makes holds a newline, when no line
# of the file and no vendored hash does
law lines_clear:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, String>
  for +el: {Str.clear.all(ls, '\n') == True{} : Bool}
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {Str.clear.all(I.lines(ds, ls), '\n') == True{} : Bool}

def lines_clear(ds, ls, el, ev):
  walk_clear(ls, I.rules(I.tag(ls)), I.block(ds, I.tag(ls)), False{}, el,
    rules_clear(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
      I.has(I.tag(ls), I.Pkgs{})),
    block_clear(ds, I.tag(ls), ev))

# LAW: the file `sync` writes, with whether its lines changed given as a
# parameter, reads back as the lines `I.lines` made from the file it read.
# Unchanged lines leave the file as it was, whose lines were those already.
law sync_lines.arm:
  for +ds: List<&2, M.Dep>
  for +text: String
  for b: Bool
  for eb: {String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
    I.file.text(I.file.lines(text))) == b : Bool}
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.file.lines(I.text.out(b, text, I.file.text(I.lines(ds, I.file.lines(text)))))
    == I.lines(ds, I.file.lines(text)) : List<&2, String>}

def sync_lines.arm(ds, text, b, eb, ev):
  match b:
    case True{}:
      Equal.sym(List<&2, String>, I.lines(ds, I.file.lines(text)), I.file.lines(text),
        Equal.trans(List<&2, String>,
          I.lines(ds, I.file.lines(text)),
          I.file.lines(I.file.text(I.lines(ds, I.file.lines(text)))),
          I.file.lines(text),
          Equal.sym(List<&2, String>,
            I.file.lines(I.file.text(I.lines(ds, I.file.lines(text)))),
            I.lines(ds, I.file.lines(text)),
            file_lines_text(I.lines(ds, I.file.lines(text)),
              lines_clear(ds, I.file.lines(text), file_lines_clear(text), ev))),
          Equal.trans(List<&2, String>,
            I.file.lines(I.file.text(I.lines(ds, I.file.lines(text)))),
            I.file.lines(I.file.text(I.file.lines(text))),
            I.file.lines(text),
            Equal.cong(String, List<&2, String>, x => I.file.lines(x),
              I.file.text(I.lines(ds, I.file.lines(text))),
              I.file.text(I.file.lines(text)),
              Str.string_eq_true(I.file.text(I.lines(ds, I.file.lines(text))),
                I.file.text(I.file.lines(text)), eb)),
            file_lines_text(I.file.lines(text), file_lines_clear(text)))))
    case False{}:
      file_lines_text(I.lines(ds, I.file.lines(text)),
        lines_clear(ds, I.file.lines(text), file_lines_clear(text), ev))

# LAW: the file `sync` writes reads back as the lines `I.lines` made from the
# file it read, whatever that file ended with
law sync_lines:
  for +ds: List<&2, M.Dep>
  for +text: String
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.file.lines(I.sync(ds, text)) == I.lines(ds, I.file.lines(text))
    : List<&2, String>}

def sync_lines(ds, text, ev):
  sync_lines.arm(ds, text,
    String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
      I.file.text(I.file.lines(text))), {==}, ev)

# The file's lines are what `I.lines` made, so the line laws hold of it.
def Laws.sync_allowlist_is_the_ledger(ds, text, ev):
  Equal.trans(List<&2, String>,
    I.hashes(I.file.lines(I.sync(ds, text))),
    I.hashes(I.lines(ds, I.file.lines(text))),
    I.vended(ds),
    Equal.cong(List<&2, String>, List<&2, String>, y => I.hashes(y),
      I.file.lines(I.sync(ds, text)), I.lines(ds, I.file.lines(text)),
      sync_lines(ds, text, ev)),
    Laws.allowlist_is_the_ledger(ds, I.file.lines(text)))

def Laws.sync_keeps_other_lines(ds, text, ev):
  Equal.trans(List<&2, String>,
    I.others(I.file.lines(I.sync(ds, text))),
    I.others(I.lines(ds, I.file.lines(text))),
    I.others(I.file.lines(text)),
    Equal.cong(List<&2, String>, List<&2, String>, y => I.others(y),
      I.file.lines(I.sync(ds, text)), I.lines(ds, I.file.lines(text)),
      sync_lines(ds, text, ev)),
    Laws.allowlist_keeps_other_lines(ds, I.file.lines(text)))

# Each hash once. The walk keeps a hash only when it has not seen it, and
# every hash it keeps after that is one it had not seen either, so none of
# them is the hash it kept.

# LAW: the negation of a bit that answered False
law not_of_false:
  for x: Bool
  for e: {x == False{} : Bool}
  {Bool.not(x) == True{} : Bool}

def not_of_false(x, e):
  %Equal.sym(Bool, x, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

# whether no hash of a list is one `seen` names. Law vocabulary: ez never
# calls it.
def fresh(hs: List<&2, String>, +seen: List<&2, String>) -> Bool:
  match hs:
    case []:
      True{}
    case +h <> t:
      +rest = fresh(t, seen)
      Bool.and(Bool.not(I.named(seen, h)), rest)

# LAW: two strings that compare unequal compare unequal the other way round
law eq_flip:
  for +a: String
  for +b: String
  for e: {String.eq(a, b) == False{} : Bool}
  {String.eq(b, a) == False{} : Bool}

# LAW: the same, with how the other comparison went given as a parameter
law eq_flip.arm:
  for +a: String
  for +b: String
  for c: Bool
  for ec: {String.eq(b, a) == c : Bool}
  for e: {String.eq(a, b) == False{} : Bool}
  {String.eq(b, a) == False{} : Bool}

def eq_flip.arm(a, b, c, ec, e):
  match c:
    case False{}:
      ec
    case True{}:
      Eq.bit.absurd(&2, {String.eq(b, a) == False{} : Bool},
        Equal.trans(Bool, False{}, String.eq(a, a), True{},
          Equal.trans(Bool, False{}, String.eq(a, b), String.eq(a, a),
            Equal.sym(Bool, String.eq(a, b), False{}, e),
            Equal.cong(String, Bool, x => String.eq(a, x), b, a,
              Str.string_eq_true(b, a, ec))),
          Eq.string_eq_self(a)))

def eq_flip(a, b, e):
  eq_flip.arm(a, b, String.eq(b, a), {==}, e)

# LAW: a list none of whose hashes `h <> seen` names has none `seen` names
law fresh_drop:
  for xs: List<&2, String>
  for +h: String
  for +seen: List<&2, String>
  for +e: {fresh(xs, h <> seen) == True{} : Bool}
  {fresh(xs, seen) == True{} : Bool}

def fresh_drop(xs, h, seen, e):
  match xs:
    case []:
      {==}
    case +x <> +r:
      and_tt(Bool.not(I.named(seen, x)), fresh(r, seen),
        not_of_false(I.named(seen, x),
          or_right(String.eq(h, x), I.named(seen, x),
            Eq.not.true(Bool.or(String.eq(h, x), I.named(seen, x)),
              Eq.and.left(Bool.not(Bool.or(String.eq(h, x), I.named(seen, x))),
                fresh(r, h <> seen), e)))),
        fresh_drop(r, h, seen,
          Eq.and.right(Bool.not(Bool.or(String.eq(h, x), I.named(seen, x))),
            fresh(r, h <> seen), e)))

# LAW: and does not name `h`
law fresh_miss:
  for xs: List<&2, String>
  for +h: String
  for +seen: List<&2, String>
  for +e: {fresh(xs, h <> seen) == True{} : Bool}
  {I.named(xs, h) == False{} : Bool}

def fresh_miss(xs, h, seen, e):
  match xs:
    case []:
      {==}
    case +x <> +r:
      %Equal.sym(Bool, String.eq(x, h), False{},
        eq_flip(h, x,
          or_left(String.eq(h, x), I.named(seen, x),
            Eq.not.true(Bool.or(String.eq(h, x), I.named(seen, x)),
              Eq.and.left(Bool.not(Bool.or(String.eq(h, x), I.named(seen, x))),
                fresh(r, h <> seen), e)))))
        : {Bool.or(_, I.named(r, h)) == False{} : Bool}
      fresh_miss(r, h, seen,
        Eq.and.right(Bool.not(Bool.or(String.eq(h, x), I.named(seen, x))),
          fresh(r, h <> seen), e))

# LAW: one hash of the walk, with whether it is passed over given as a
# parameter: what it keeps is none of what it has seen
law fresh_once.arm:
  for +h: String
  for +t: List<&2, String>
  for +seen: List<&2, String>
  for skip: Bool
  for es: {Bool.or(String.is_empty(h), I.named(seen, h)) == skip : Bool}
  for ih: {fresh(I.once.go(t, I.once.seen(skip, h, seen)), I.once.seen(skip, h, seen))
    == True{} : Bool}
  {fresh(I.once.put(skip, h, I.once.go(t, I.once.seen(skip, h, seen))), seen)
    == True{} : Bool}

def fresh_once.arm(h, t, seen, skip, es, ih):
  match skip:
    case True{}:
      ih
    case False{}:
      and_tt(Bool.not(I.named(seen, h)), fresh(I.once.go(t, h <> seen), seen),
        not_of_false(I.named(seen, h),
          or_right(String.is_empty(h), I.named(seen, h), es)),
        fresh_drop(I.once.go(t, h <> seen), h, seen, ih))

# LAW: nothing the walk keeps is a hash it was told it had seen
law fresh_once:
  for hs: List<&2, String>
  for +seen: List<&2, String>
  {fresh(I.once.go(hs, seen), seen) == True{} : Bool}

def fresh_once(hs, seen):
  match hs:
    case []:
      {==}
    case +h <> +t:
      fresh_once.arm(h, t, seen, Bool.or(String.is_empty(h), I.named(seen, h)), {==},
        fresh_once(t, I.once.seen(Bool.or(String.is_empty(h), I.named(seen, h)), h, seen)))

# LAW: one hash of the walk, with whether it is passed over given as a
# parameter: a kept hash is none of the hashes kept after it
law once_distinct.arm:
  for +h: String
  for +t: List<&2, String>
  for +seen: List<&2, String>
  for skip: Bool
  for ih: {Laws.distinct(I.once.go(t, I.once.seen(skip, h, seen))) == True{} : Bool}
  {Laws.distinct(I.once.put(skip, h, I.once.go(t, I.once.seen(skip, h, seen))))
    == True{} : Bool}

def once_distinct.arm(h, t, seen, skip, ih):
  match skip:
    case True{}:
      ih
    case False{}:
      and_tt(Bool.not(I.named(I.once.go(t, h <> seen), h)),
        Laws.distinct(I.once.go(t, h <> seen)),
        not_of_false(I.named(I.once.go(t, h <> seen), h),
          fresh_miss(I.once.go(t, h <> seen), h, seen, fresh_once(t, h <> seen))),
        ih)

# LAW: the walk keeps each hash once
law once_distinct:
  for hs: List<&2, String>
  for +seen: List<&2, String>
  {Laws.distinct(I.once.go(hs, seen)) == True{} : Bool}

def once_distinct(hs, seen):
  match hs:
    case []:
      {==}
    case +h <> +t:
      once_distinct.arm(h, t, seen, Bool.or(String.is_empty(h), I.named(seen, h)),
        once_distinct(t, I.once.seen(Bool.or(String.is_empty(h), I.named(seen, h)), h, seen)))

def Laws.vended_once(ds):
  once_distinct(I.vendors(ds), [])

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

# whether the walk keeps every line of a list as it is
def kept.all(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      True{}
    case +h <> t:
      +rest = kept.all(t)
      Bool.and(keeps(I.kind(h)), rest)

# whether a kind of line is an allowlist line
def allowed(k: I.Rule) -> Bool:
  match k:
    case I.Other{}:
      False{}
    case I.Dir{}:
      False{}
    case I.Star{}:
      False{}
    case I.Lib{}:
      False{}
    case I.Pkgs{}:
      False{}
    case I.Allow{_h}:
      True{}

# whether every line of a list is an allowlist line
def allowed.all(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      True{}
    case +h <> t:
      +rest = allowed.all(t)
      Bool.and(allowed(I.kind(h)), rest)

# LAW: where the brackets fall in a run of lines does not change the run
law lines_assoc:
  for a: List<&2, String>
  for +b: List<&2, String>
  for +c: List<&2, String>
  {List.append(&2, String, List.append(&2, String, a, b), c)
    == List.append(&2, String, a, List.append(&2, String, b, c)) : List<&2, String>}

def lines_assoc(a, b, c):
  match a:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        List.append(&2, String, List.append(&2, String, t, b), c),
        List.append(&2, String, t, List.append(&2, String, b, c)),
        lines_assoc(t, b, c))

# LAW: two runs are kept exactly when each is
law kept_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  {kept.all(List.append(&2, String, xs, ys))
    == Bool.and(kept.all(xs), kept.all(ys)) : Bool}

def kept_app(xs, ys):
  match xs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(Bool, kept.all(List.append(&2, String, t, ys)),
        Bool.and(kept.all(t), kept.all(ys)), kept_app(t, ys))
        : {Bool.and(keeps(I.kind(h)), _)
          == Bool.and(Bool.and(keeps(I.kind(h)), kept.all(t)), kept.all(ys)) : Bool}
      Str.and_assoc(keeps(I.kind(h)), kept.all(t), kept.all(ys))

# LAW: and so two kept runs are kept together
law kept_both:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for ex: {kept.all(xs) == True{} : Bool}
  for ey: {kept.all(ys) == True{} : Bool}
  {kept.all(List.append(&2, String, xs, ys)) == True{} : Bool}

def kept_both(xs, ys, ex, ey):
  Equal.trans(Bool, kept.all(List.append(&2, String, xs, ys)),
    Bool.and(kept.all(xs), kept.all(ys)), True{},
    kept_app(xs, ys), and_tt(kept.all(xs), kept.all(ys), ex, ey))

# LAW: one line of a kept run, with its kind given as a parameter: it is
# kept, in front of the rest
law walk_kept.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for e: {keeps(k) == True{} : Bool}
  for ih: {I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d)
    == List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)) : List<&2, String>}
  {I.walk(I.Line{k, h} <> I.tag(List.append(&2, String, t, z)), fix, blk, d)
    == h <> List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)) : List<&2, String>}

def walk_kept.arm(k, h, t, z, fix, blk, d, e, ih):
  match k:
    case I.Other{}:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d),
        List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)), ih)
    case I.Star{}:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d),
        List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)), ih)
    case I.Lib{}:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d),
        List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)), ih)
    case I.Pkgs{}:
      Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
        I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, d),
        List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d)), ih)
    case I.Dir{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Dir{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, d) == h <> List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d))
        : List<&2, String>}, e)
    case I.Allow{x}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Allow{x}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, d) == h <> List.append(&2, String, t, I.walk(I.tag(z), fix, blk, d))
        : List<&2, String>}, e)

# LAW: a run of lines the walk keeps as they are comes out as it went in,
# whatever follows it
law walk_kept:
  for +xs: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +e: {kept.all(xs) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, xs, z)), fix, blk, d)
    == List.append(&2, String, xs, I.walk(I.tag(z), fix, blk, d)) : List<&2, String>}

def walk_kept(xs, z, fix, blk, d, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      walk_kept.arm(I.kind(h), h, t, z, fix, blk, d,
        Eq.and.left(keeps(I.kind(h)), kept.all(t), e),
        walk_kept(t, z, fix, blk, d, Eq.and.right(keeps(I.kind(h)), kept.all(t), e)))

# LAW: a kept run, all of it, is itself and then the block, if still owed
law walk_clean:
  for +xs: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +e: {kept.all(xs) == True{} : Bool}
  {I.walk(I.tag(xs), fix, blk, d) == List.append(&2, String, xs, I.placed(d, blk))
    : List<&2, String>}

def walk_clean(xs, fix, blk, d, e):
  Equal.trans(List<&2, String>,
    I.walk(I.tag(xs), fix, blk, d),
    I.walk(I.tag(List.append(&2, String, xs, [])), fix, blk, d),
    List.append(&2, String, xs, I.placed(d, blk)),
    Equal.cong(List<&2, String>, List<&2, String>, y => I.walk(I.tag(y), fix, blk, d),
      xs, List.append(&2, String, xs, []),
      Equal.sym(List<&2, String>, List.append(&2, String, xs, []), xs, lines_app_nil(xs))),
    walk_kept(xs, [], fix, blk, d, e))

# LAW: one allowlist line, once the block is down, with its kind given as a
# parameter: it is dropped
law walk_drop.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for e: {allowed(k) == True{} : Bool}
  for ih: {I.walk(I.tag(List.append(&2, String, t, z)), fix, blk, True{})
    == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}
  {I.walk(I.Line{k, h} <> I.tag(List.append(&2, String, t, z)), fix, blk, True{})
    == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}

def walk_drop.arm(k, h, t, z, fix, blk, e, ih):
  match k:
    case I.Allow{x}:
      ih
    case I.Other{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Other{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)
    case I.Dir{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Dir{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)
    case I.Star{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Star{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)
    case I.Lib{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Lib{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)
    case I.Pkgs{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Pkgs{}, h} <> I.tag(List.append(&2, String, t, z)),
        fix, blk, True{}) == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}, e)

# LAW: a run of allowlist lines, once the block is down, is dropped
law walk_drop:
  for +xs: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +e: {allowed.all(xs) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, xs, z)), fix, blk, True{})
    == I.walk(I.tag(z), fix, blk, True{}) : List<&2, String>}

def walk_drop(xs, z, fix, blk, e):
  match xs:
    case []:
      {==}
    case +h <> +t:
      walk_drop.arm(I.kind(h), h, t, z, fix, blk,
        Eq.and.left(allowed(I.kind(h)), allowed.all(t), e),
        walk_drop(t, z, fix, blk, Eq.and.right(allowed(I.kind(h)), allowed.all(t), e)))

# LAW: the first allowlist line of a run of them, with its kind given as a
# parameter: the block goes down in its place, and the rest are dropped
law first_allow.arm:
  for k: I.Rule
  for +a1: String
  for +as: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for e: {allowed(k) == True{} : Bool}
  for +ea: {allowed.all(as) == True{} : Bool}
  {I.walk(I.Line{k, a1} <> I.tag(List.append(&2, String, as, z)), fix, blk, False{})
    == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{})) : List<&2, String>}

def first_allow.arm(k, a1, as, z, fix, blk, e, ea):
  match k:
    case I.Allow{x}:
      Equal.cong(List<&2, String>, List<&2, String>, y => List.append(&2, String, blk, y),
        I.walk(I.tag(List.append(&2, String, as, z)), fix, blk, True{}),
        I.walk(I.tag(z), fix, blk, True{}),
        walk_drop(as, z, fix, blk, ea))
    case I.Other{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Other{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)
    case I.Dir{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Dir{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)
    case I.Star{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Star{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)
    case I.Lib{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Lib{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)
    case I.Pkgs{}:
      Eq.bit.absurd(&2, {I.walk(I.Line{I.Pkgs{}, a1} <> I.tag(List.append(&2, String, as, z)),
        fix, blk, False{}) == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{}))
        : List<&2, String>}, e)

# LAW: a run of allowlist lines, before the block is down: the block goes
# down in their place
law first_allow:
  for +a1: String
  for +as: List<&2, String>
  for +z: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +e: {allowed.all(a1 <> as) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, a1 <> as, z)), fix, blk, False{})
    == List.append(&2, String, blk, I.walk(I.tag(z), fix, blk, True{})) : List<&2, String>}

def first_allow(a1, as, z, fix, blk, e):
  first_allow.arm(I.kind(a1), a1, as, z, fix, blk,
    Eq.and.left(allowed(I.kind(a1)), allowed.all(as), e),
    Eq.and.right(allowed(I.kind(a1)), allowed.all(as), e))

# LAW: one line of the walk, with its kind given as a parameter: what it puts
# in the line's place is kept as it is, when the rules are and the block is
# already down
law walk_kept_out.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +ef: {kept.all(fix) == True{} : Bool}
  for +ep: {kept.all(I.placed(d, blk)) == True{} : Bool}
  for ihd: {kept.all(I.walk(I.tag(t), fix, blk, d)) == True{} : Bool}
  for iht: {kept.all(I.walk(I.tag(t), fix, blk, True{})) == True{} : Bool}
  {kept.all(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d)) == True{} : Bool}

def walk_kept_out.arm(k, h, t, fix, blk, d, ek, ef, ep, ihd, iht):
  match k:
    case I.Other{}:
      %Equal.sym(I.Rule, I.kind(h), I.Other{}, ek)
        : {Bool.and(keeps(_), kept.all(I.walk(I.tag(t), fix, blk, d))) == True{} : Bool}
      ihd
    case I.Star{}:
      %Equal.sym(I.Rule, I.kind(h), I.Star{}, ek)
        : {Bool.and(keeps(_), kept.all(I.walk(I.tag(t), fix, blk, d))) == True{} : Bool}
      ihd
    case I.Lib{}:
      %Equal.sym(I.Rule, I.kind(h), I.Lib{}, ek)
        : {Bool.and(keeps(_), kept.all(I.walk(I.tag(t), fix, blk, d))) == True{} : Bool}
      ihd
    case I.Pkgs{}:
      %Equal.sym(I.Rule, I.kind(h), I.Pkgs{}, ek)
        : {Bool.and(keeps(_), kept.all(I.walk(I.tag(t), fix, blk, d))) == True{} : Bool}
      ihd
    case I.Dir{}:
      kept_both(fix, I.walk(I.tag(t), fix, blk, d), ef, ihd)
    case I.Allow{x}:
      kept_both(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}), ep, iht)

# LAW: what the walk writes is kept as it is, when the rules are and the
# block, if it still goes down, is too
law walk_kept_out:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +ef: {kept.all(fix) == True{} : Bool}
  for +ep: {kept.all(I.placed(d, blk)) == True{} : Bool}
  {kept.all(I.walk(I.tag(raw), fix, blk, d)) == True{} : Bool}

def walk_kept_out(raw, fix, blk, d, ef, ep):
  match raw:
    case []:
      ep
    case +h <> +t:
      walk_kept_out.arm(I.kind(h), h, t, fix, blk, d, {==}, ef, ep,
        walk_kept_out(t, fix, blk, d, ef, ep),
        walk_kept_out(t, fix, blk, True{}, ef, {==}))

# LAW: an empty block, put down or not, is nothing
law placed_nil:
  for +d: Bool
  {I.placed(d, []) == [] : List<&2, String>}

def placed_nil(d):
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: the second run over what the first wrote, once the block is down or
# holds nothing: every line is kept, and nothing is added
law idem_nil:
  for +raw: List<&2, String>
  for +fix: List<&2, String>
  for +fix2: List<&2, String>
  for +d: Bool
  for +d2: Bool
  for +ef: {kept.all(fix) == True{} : Bool}
  {I.walk(I.tag(I.walk(I.tag(raw), fix, [], d)), fix2, [], d2)
    == I.walk(I.tag(raw), fix, [], d) : List<&2, String>}

def idem_nil(raw, fix, fix2, d, d2, ef):
  Equal.trans(List<&2, String>,
    I.walk(I.tag(I.walk(I.tag(raw), fix, [], d)), fix2, [], d2),
    List.append(&2, String, I.walk(I.tag(raw), fix, [], d), I.placed(d2, [])),
    I.walk(I.tag(raw), fix, [], d),
    walk_clean(I.walk(I.tag(raw), fix, [], d), fix2, [], d2,
      walk_kept_out(raw, fix, [], d, ef,
        Equal.cong(List<&2, String>, Bool, y => kept.all(y), I.placed(d, []), [],
          placed_nil(d)))),
    Equal.trans(List<&2, String>,
      List.append(&2, String, I.walk(I.tag(raw), fix, [], d), I.placed(d2, [])),
      List.append(&2, String, I.walk(I.tag(raw), fix, [], d), []),
      I.walk(I.tag(raw), fix, [], d),
      Equal.cong(List<&2, String>, List<&2, String>,
        y => List.append(&2, String, I.walk(I.tag(raw), fix, [], d), y),
        I.placed(d2, []), [], placed_nil(d2)),
      lines_app_nil(I.walk(I.tag(raw), fix, [], d))))

# LAW: the second run over a block of rules and allowlist lines, whose own
# block is those allowlist lines: it gives the block back
law idem_block:
  for +n: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +fix2: List<&2, String>
  for +en: {kept.all(n) == True{} : Bool}
  for +ea: {allowed.all(a1 <> as) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, n, a1 <> as)), fix2, a1 <> as, False{})
    == List.append(&2, String, n, a1 <> as) : List<&2, String>}

def idem_block(n, a1, as, fix2, en, ea):
  Equal.trans(List<&2, String>,
    I.walk(I.tag(List.append(&2, String, n, a1 <> as)), fix2, a1 <> as, False{}),
    List.append(&2, String, n, I.walk(I.tag(a1 <> as), fix2, a1 <> as, False{})),
    List.append(&2, String, n, a1 <> as),
    walk_kept(n, a1 <> as, fix2, a1 <> as, False{}, en),
    Equal.cong(List<&2, String>, List<&2, String>, y => List.append(&2, String, n, y),
      I.walk(I.tag(a1 <> as), fix2, a1 <> as, False{}), a1 <> as,
      Equal.trans(List<&2, String>,
        I.walk(I.tag(a1 <> as), fix2, a1 <> as, False{}),
        I.walk(I.tag(List.append(&2, String, a1 <> as, [])), fix2, a1 <> as, False{}),
        a1 <> as,
        Equal.cong(List<&2, String>, List<&2, String>,
          y => I.walk(I.tag(y), fix2, a1 <> as, False{}),
          a1 <> as, List.append(&2, String, a1 <> as, []),
          Equal.sym(List<&2, String>, List.append(&2, String, a1 <> as, []), a1 <> as,
            lines_app_nil(a1 <> as))),
        Equal.trans(List<&2, String>,
          I.walk(I.tag(List.append(&2, String, a1 <> as, [])), fix2, a1 <> as, False{}),
          List.append(&2, String, a1 <> as, I.walk(I.tag([]), fix2, a1 <> as, True{})),
          a1 <> as,
          first_allow(a1, as, [], fix2, a1 <> as, ea),
          lines_app_nil(a1 <> as)))))

# LAW: the second run over the block the first put down in an allowlist
# line's place, and what the first wrote after it: the block comes back
# where it was, and the rest is kept
law idem_allow:
  for +n: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +r: List<&2, String>
  for +fix2: List<&2, String>
  for +en: {kept.all(n) == True{} : Bool}
  for +ea: {allowed.all(a1 <> as) == True{} : Bool}
  for +er: {kept.all(r) == True{} : Bool}
  {I.walk(I.tag(List.append(&2, String, List.append(&2, String, n, a1 <> as), r)),
    fix2, a1 <> as, False{})
    == List.append(&2, String, List.append(&2, String, n, a1 <> as), r) : List<&2, String>}

def idem_allow(n, a1, as, r, fix2, en, ea, er):
  Equal.trans(List<&2, String>,
    I.walk(I.tag(List.append(&2, String, List.append(&2, String, n, a1 <> as), r)),
      fix2, a1 <> as, False{}),
    I.walk(I.tag(List.append(&2, String, n, List.append(&2, String, a1 <> as, r))),
      fix2, a1 <> as, False{}),
    List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
    Equal.cong(List<&2, String>, List<&2, String>,
      y => I.walk(I.tag(y), fix2, a1 <> as, False{}),
      List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
      List.append(&2, String, n, List.append(&2, String, a1 <> as, r)),
      lines_assoc(n, a1 <> as, r)),
    Equal.trans(List<&2, String>,
      I.walk(I.tag(List.append(&2, String, n, List.append(&2, String, a1 <> as, r))),
        fix2, a1 <> as, False{}),
      List.append(&2, String, n,
        I.walk(I.tag(List.append(&2, String, a1 <> as, r)), fix2, a1 <> as, False{})),
      List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
      walk_kept(n, List.append(&2, String, a1 <> as, r), fix2, a1 <> as, False{}, en),
      Equal.trans(List<&2, String>,
        List.append(&2, String, n,
          I.walk(I.tag(List.append(&2, String, a1 <> as, r)), fix2, a1 <> as, False{})),
        List.append(&2, String, n, List.append(&2, String, a1 <> as, r)),
        List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
        Equal.cong(List<&2, String>, List<&2, String>, y => List.append(&2, String, n, y),
          I.walk(I.tag(List.append(&2, String, a1 <> as, r)), fix2, a1 <> as, False{}),
          List.append(&2, String, a1 <> as, r),
          Equal.trans(List<&2, String>,
            I.walk(I.tag(List.append(&2, String, a1 <> as, r)), fix2, a1 <> as, False{}),
            List.append(&2, String, a1 <> as, I.walk(I.tag(r), fix2, a1 <> as, True{})),
            List.append(&2, String, a1 <> as, r),
            first_allow(a1, as, r, fix2, a1 <> as, ea),
            Equal.cong(List<&2, String>, List<&2, String>,
              y => List.append(&2, String, a1 <> as, y),
              I.walk(I.tag(r), fix2, a1 <> as, True{}), r,
              Equal.trans(List<&2, String>,
                I.walk(I.tag(r), fix2, a1 <> as, True{}),
                List.append(&2, String, r, []),
                r,
                walk_clean(r, fix2, a1 <> as, True{}, er),
                lines_app_nil(r))))),
        Equal.sym(List<&2, String>,
          List.append(&2, String, List.append(&2, String, n, a1 <> as), r),
          List.append(&2, String, n, List.append(&2, String, a1 <> as, r)),
          lines_assoc(n, a1 <> as, r)))))

# LAW: one line of the first run, with its kind given as a parameter: the
# second run, whose block is the first run's allowlist lines, gives back
# what the first wrote for it and after it
law idem_walk.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +n: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +fix2: List<&2, String>
  for ek: {I.kind(h) == k : I.Rule}
  for +ef: {kept.all(fix) == True{} : Bool}
  for +en: {kept.all(n) == True{} : Bool}
  for +ea: {allowed.all(a1 <> as) == True{} : Bool}
  for ih: {I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
    fix2, a1 <> as, False{})
    == I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}) : List<&2, String>}
  {I.walk(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, List.append(&2, String, n, a1 <> as),
    False{})), fix2, a1 <> as, False{})
    == I.walk(I.Line{k, h} <> I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})
    : List<&2, String>}

def idem_walk.arm(k, h, t, fix, n, a1, as, fix2, ek, ef, en, ea, ih):
  match k:
    case I.Other{}:
      Equal.trans(List<&2, String>,
        I.walk(I.Line{I.kind(h), h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        I.walk(I.Line{I.Other{}, h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        h <> I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
        Equal.cong(I.Rule, List<&2, String>,
          q => I.walk(I.Line{q, h} <> I.tag(I.walk(I.tag(t), fix,
            List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
          I.kind(h), I.Other{}, ek),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Star{}:
      Equal.trans(List<&2, String>,
        I.walk(I.Line{I.kind(h), h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        I.walk(I.Line{I.Star{}, h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        h <> I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
        Equal.cong(I.Rule, List<&2, String>,
          q => I.walk(I.Line{q, h} <> I.tag(I.walk(I.tag(t), fix,
            List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
          I.kind(h), I.Star{}, ek),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Lib{}:
      Equal.trans(List<&2, String>,
        I.walk(I.Line{I.kind(h), h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        I.walk(I.Line{I.Lib{}, h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        h <> I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
        Equal.cong(I.Rule, List<&2, String>,
          q => I.walk(I.Line{q, h} <> I.tag(I.walk(I.tag(t), fix,
            List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
          I.kind(h), I.Lib{}, ek),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Pkgs{}:
      Equal.trans(List<&2, String>,
        I.walk(I.Line{I.kind(h), h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        I.walk(I.Line{I.Pkgs{}, h} <> I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
        h <> I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
        Equal.cong(I.Rule, List<&2, String>,
          q => I.walk(I.Line{q, h} <> I.tag(I.walk(I.tag(t), fix,
            List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{}),
          I.kind(h), I.Pkgs{}, ek),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Dir{}:
      Equal.trans(List<&2, String>,
        I.walk(I.tag(List.append(&2, String, fix,
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}))),
          fix2, a1 <> as, False{}),
        List.append(&2, String, fix, I.walk(I.tag(I.walk(I.tag(t), fix,
          List.append(&2, String, n, a1 <> as), False{})), fix2, a1 <> as, False{})),
        List.append(&2, String, fix,
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
        walk_kept(fix, I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}),
          fix2, a1 <> as, False{}, ef),
        Equal.cong(List<&2, String>, List<&2, String>, y => List.append(&2, String, fix, y),
          I.walk(I.tag(I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{})),
            fix2, a1 <> as, False{}),
          I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), False{}), ih))
    case I.Allow{x}:
      idem_allow(n, a1, as,
        I.walk(I.tag(t), fix, List.append(&2, String, n, a1 <> as), True{}), fix2, en, ea,
        walk_kept_out(t, fix, List.append(&2, String, n, a1 <> as), True{}, ef, {==}))

# LAW: the second run, whose block is the first run's allowlist lines, gives
# back what the first run wrote, when the first run's rules and the rules in
# front of its block are kept as they are
law idem_walk:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +n: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +fix2: List<&2, String>
  for +ef: {kept.all(fix) == True{} : Bool}
  for +en: {kept.all(n) == True{} : Bool}
  for +ea: {allowed.all(a1 <> as) == True{} : Bool}
  {I.walk(I.tag(I.walk(I.tag(raw), fix, List.append(&2, String, n, a1 <> as), False{})),
    fix2, a1 <> as, False{})
    == I.walk(I.tag(raw), fix, List.append(&2, String, n, a1 <> as), False{})
    : List<&2, String>}

def idem_walk(raw, fix, n, a1, as, fix2, ef, en, ea):
  match raw:
    case []:
      idem_block(n, a1, as, fix2, en, ea)
    case +h <> +t:
      idem_walk.arm(I.kind(h), h, t, fix, n, a1, as, fix2, {==}, ef, en, ea,
        idem_walk(t, fix, n, a1, as, fix2, ef, en, ea))

# What the first run's output holds: no `.ez/` line, and each of the three
# rules when it holds a hash. A rule the file had is kept where it was; one it
# lacked went in where its `.ez/` line was, or in front of the block.

# LAW: an `or` of a bit and False is the bit
law or_false:
  for a: Bool
  {Bool.or(a, False{}) == a : Bool}

def or_false(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: an `or` of a bit and True is True
law or_true:
  for a: Bool
  {Bool.or(a, True{}) == True{} : Bool}

def or_true(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: an `or` of two halves that answered False
law or_ff:
  for a: Bool
  for b: Bool
  for ea: {a == False{} : Bool}
  for eb: {b == False{} : Bool}
  {Bool.or(a, b) == False{} : Bool}

def or_ff(a, b, ea, eb):
  %Equal.sym(Bool, a, False{}, ea) : {Bool.or(_, b) == False{} : Bool}
  eb

# LAW: a scan that stops at a hit answers True, and one that goes on answers
# what the rest does, whatever else is `or`ed onto the rest
law step_or:
  for b: Bool
  for x: Bool
  for y: Bool
  {I.has.step(b, _u => Bool.or(x, y)) == Bool.or(I.has.step(b, _u => x), y) : Bool}

def step_or(b, _x, _y):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a run of lines has a kind of line when either half has one
law has_app:
  for xs: List<&2, String>
  for +ys: List<&2, String>
  for +r: I.Rule
  {I.has(I.tag(List.append(&2, String, xs, ys)), r)
    == Bool.or(I.has(I.tag(xs), r), I.has(I.tag(ys), r)) : Bool}

def has_app(xs, ys, r):
  match xs:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), r), _u => I.has(I.tag(List.append(&2, String, t, ys)), r)),
        I.has.step(I.same(I.kind(h), r), _u => Bool.or(I.has(I.tag(t), r), I.has(I.tag(ys), r))),
        Bool.or(I.has.step(I.same(I.kind(h), r), _u => I.has(I.tag(t), r)), I.has(I.tag(ys), r)),
        Equal.cong(Bool, Bool, y => I.has.step(I.same(I.kind(h), r), _u => y),
          I.has(I.tag(List.append(&2, String, t, ys)), r),
          Bool.or(I.has(I.tag(t), r), I.has(I.tag(ys), r)), has_app(t, ys, r)),
        step_or(I.same(I.kind(h), r), I.has(I.tag(t), r), I.has(I.tag(ys), r)))

# LAW: a run whose front has a kind of line has it
law has_left:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +r: I.Rule
  for e: {I.has(I.tag(xs), r) == True{} : Bool}
  {I.has(I.tag(List.append(&2, String, xs, ys)), r) == True{} : Bool}

def has_left(xs, ys, r, e):
  %Equal.sym(Bool, I.has(I.tag(List.append(&2, String, xs, ys)), r),
    Bool.or(I.has(I.tag(xs), r), I.has(I.tag(ys), r)), has_app(xs, ys, r))
    : {_ == True{} : Bool}
  %Equal.sym(Bool, I.has(I.tag(xs), r), True{}, e)
    : {Bool.or(_, I.has(I.tag(ys), r)) == True{} : Bool}
  {==}

# LAW: and one whose back has it
law has_right:
  for +xs: List<&2, String>
  for +ys: List<&2, String>
  for +r: I.Rule
  for e: {I.has(I.tag(ys), r) == True{} : Bool}
  {I.has(I.tag(List.append(&2, String, xs, ys)), r) == True{} : Bool}

def has_right(xs, ys, r, e):
  %Equal.sym(Bool, I.has(I.tag(List.append(&2, String, xs, ys)), r),
    Bool.or(I.has(I.tag(xs), r), I.has(I.tag(ys), r)), has_app(xs, ys, r))
    : {_ == True{} : Bool}
  %Equal.sym(Bool, I.has(I.tag(ys), r), True{}, e)
    : {Bool.or(I.has(I.tag(xs), r), _) == True{} : Bool}
  or_true(I.has(I.tag(xs), r))

# LAW: a line in front of a run that has a kind of line leaves it with one
law has_cons.arm:
  for b: Bool
  for +w: List<&2, String>
  for +r: I.Rule
  for e: {I.has(I.tag(w), r) == True{} : Bool}
  {I.has.step(b, _u => I.has(I.tag(w), r)) == True{} : Bool}

def has_cons.arm(b, _w, _r, e):
  match b:
    case True{}:
      {==}
    case False{}:
      e

law has_cons:
  for +h: String
  for +w: List<&2, String>
  for +r: I.Rule
  for e: {I.has(I.tag(w), r) == True{} : Bool}
  {I.has(I.tag(h <> w), r) == True{} : Bool}

def has_cons(h, w, r, e):
  has_cons.arm(I.same(I.kind(h), r), w, r, e)

# LAW: a line of the kind in front of any run is one
law has_here:
  for +h: String
  for +w: List<&2, String>
  for +r: I.Rule
  for e: {I.same(I.kind(h), r) == True{} : Bool}
  {I.has(I.tag(h <> w), r) == True{} : Bool}

def has_here(h, w, r, e):
  %Equal.sym(Bool, I.same(I.kind(h), r), True{}, e)
    : {I.has.step(_, _u => I.has(I.tag(w), r)) == True{} : Bool}
  {==}

# LAW: a line that is not of the kind leaves the question to the rest
law has_rest:
  for +h: String
  for +t: List<&2, String>
  for +r: I.Rule
  for es: {I.same(I.kind(h), r) == False{} : Bool}
  for e: {I.has(I.tag(h <> t), r) == True{} : Bool}
  {I.has(I.tag(t), r) == True{} : Bool}

def has_rest(h, t, r, es, e):
  Equal.trans(Bool,
    I.has(I.tag(t), r),
    I.has.step(I.same(I.kind(h), r), _u => I.has(I.tag(t), r)),
    True{},
    Equal.cong(Bool, Bool, c => I.has.step(c, _u => I.has(I.tag(t), r)),
      False{}, I.same(I.kind(h), r), Equal.sym(Bool, I.same(I.kind(h), r), False{}, es)),
    e)

# LAW: `.ez/` is none of the kinds the walk keeps
law same_dir_kept:
  for r: I.Rule
  for kr: {keeps(r) == True{} : Bool}
  {I.same(I.Dir{}, r) == False{} : Bool}

def same_dir_kept(r, kr):
  match r:
    case I.Other{}:
      {==}
    case I.Dir{}:
      Eq.bit.absurd(&2, {I.same(I.Dir{}, I.Dir{}) == False{} : Bool}, kr)
    case I.Star{}:
      {==}
    case I.Lib{}:
      {==}
    case I.Pkgs{}:
      {==}
    case I.Allow{x}:
      Eq.bit.absurd(&2, {I.same(I.Dir{}, I.Allow{x}) == False{} : Bool}, kr)

# LAW: and an allowlist line is no kind `same` is asked about
law same_allow:
  for +x: String
  for r: I.Rule
  {I.same(I.Allow{x}, r) == False{} : Bool}

def same_allow(_x, r):
  match r:
    case I.Other{}:
      {==}
    case I.Dir{}:
      {==}
    case I.Star{}:
      {==}
    case I.Lib{}:
      {==}
    case I.Pkgs{}:
      {==}
    case I.Allow{y}:
      {==}

# LAW: one line, with how its kind compares given as a parameter: a line of
# the kind in front of what the walk wrote is one, and otherwise the rest had
# one, which the walk kept
law has_kept.cons.arm:
  for b: Bool
  for +h: String
  for +t: List<&2, String>
  for +w: List<&2, String>
  for +r: I.Rule
  for eb: {I.same(I.kind(h), r) == b : Bool}
  for e: {I.has.step(b, _u => I.has(I.tag(t), r)) == True{} : Bool}
  for ih: {I.has(I.tag(t), r) == True{} : Bool} -> {I.has(I.tag(w), r) == True{} : Bool}
  {I.has(I.tag(h <> w), r) == True{} : Bool}

def has_kept.cons.arm(b, h, t, w, r, eb, e, ih):
  match b:
    case True{}:
      has_here(h, w, r, eb)
    case False{}:
      has_cons(h, w, r, ih(e))

# LAW: one line of the walk, with its kind given as a parameter: a kind the
# walk keeps is still there after it
law has_kept.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +kr: {keeps(r) == True{} : Bool}
  for e: {I.has(I.tag(h <> t), r) == True{} : Bool}
  for ihd: {I.has(I.tag(t), r) == True{} : Bool}
    -> {I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), r) == True{} : Bool}
  for iht: {I.has(I.tag(t), r) == True{} : Bool}
    -> {I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d)), r) == True{} : Bool}

def has_kept.arm(k, h, t, r, fix, blk, d, ek, kr, e, ihd, iht):
  match k:
    case I.Other{}:
      has_kept.cons.arm(I.same(I.kind(h), r), h, t, I.walk(I.tag(t), fix, blk, d), r,
        {==}, e, ihd)
    case I.Star{}:
      has_kept.cons.arm(I.same(I.kind(h), r), h, t, I.walk(I.tag(t), fix, blk, d), r,
        {==}, e, ihd)
    case I.Lib{}:
      has_kept.cons.arm(I.same(I.kind(h), r), h, t, I.walk(I.tag(t), fix, blk, d), r,
        {==}, e, ihd)
    case I.Pkgs{}:
      has_kept.cons.arm(I.same(I.kind(h), r), h, t, I.walk(I.tag(t), fix, blk, d), r,
        {==}, e, ihd)
    case I.Dir{}:
      has_right(fix, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, r,
          Equal.trans(Bool, I.same(I.kind(h), r), I.same(I.Dir{}, r), False{},
            Equal.cong(I.Rule, Bool, q => I.same(q, r), I.kind(h), I.Dir{}, ek),
            same_dir_kept(r, kr)), e)))
    case I.Allow{x}:
      has_right(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}), r,
        iht(has_rest(h, t, r,
          Equal.trans(Bool, I.same(I.kind(h), r), I.same(I.Allow{x}, r), False{},
            Equal.cong(I.Rule, Bool, q => I.same(q, r), I.kind(h), I.Allow{x}, ek),
            same_allow(x, r)), e)))

# LAW: a kind the walk keeps, when the file has a line of it, is in what the
# walk writes
law has_kept:
  for raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +kr: {keeps(r) == True{} : Bool}
  for e: {I.has(I.tag(raw), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, blk, d)), r) == True{} : Bool}

def has_kept(raw, r, fix, blk, d, kr, e):
  match raw:
    case []:
      Eq.bit.absurd(&2, {I.has(I.tag(I.walk(I.tag([]), fix, blk, d)), r) == True{} : Bool}, e)
    case +h <> +t:
      has_kept.arm(I.kind(h), h, t, r, fix, blk, d, {==}, kr, e,
        x => has_kept(t, r, fix, blk, d, kr, x),
        x => has_kept(t, r, fix, blk, True{}, kr, x))

# LAW: one line of the walk, with its kind given as a parameter: when the
# file has a `.ez/` line, what the rules have, what the walk writes has
law has_dir.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for e: {I.has(I.tag(h <> t), I.Dir{}) == True{} : Bool}
  for +hf: {I.has(I.tag(fix), r) == True{} : Bool}
  for ihd: {I.has(I.tag(t), I.Dir{}) == True{} : Bool}
    -> {I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), r) == True{} : Bool}
  for iht: {I.has(I.tag(t), I.Dir{}) == True{} : Bool}
    -> {I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d)), r) == True{} : Bool}

def has_dir.arm(k, h, t, r, fix, blk, d, ek, e, hf, ihd, iht):
  match k:
    case I.Dir{}:
      has_left(fix, I.walk(I.tag(t), fix, blk, d), r, hf)
    case I.Other{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Other{}, ek), e)))
    case I.Star{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Star{}, ek), e)))
    case I.Lib{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Lib{}, ek), e)))
    case I.Pkgs{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, d), r,
        ihd(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Pkgs{}, ek), e)))
    case I.Allow{x}:
      has_right(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}), r,
        iht(has_rest(h, t, I.Dir{},
          Equal.cong(I.Rule, Bool, q => I.same(q, I.Dir{}), I.kind(h), I.Allow{x}, ek), e)))

# LAW: a file with a `.ez/` line gets the rules in its place, so what they
# have, what the walk writes has
law has_dir:
  for raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for e: {I.has(I.tag(raw), I.Dir{}) == True{} : Bool}
  for +hf: {I.has(I.tag(fix), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, blk, d)), r) == True{} : Bool}

def has_dir(raw, r, fix, blk, d, e, hf):
  match raw:
    case []:
      Eq.bit.absurd(&2, {I.has(I.tag(I.walk(I.tag([]), fix, blk, d)), r) == True{} : Bool}, e)
    case +h <> +t:
      has_dir.arm(I.kind(h), h, t, r, fix, blk, d, {==}, e, hf,
        x => has_dir(t, r, fix, blk, d, x, hf),
        x => has_dir(t, r, fix, blk, True{}, x, hf))

# LAW: one line of the walk before the block is down, with its kind given as
# a parameter: what the block has, what the walk writes has
law has_blk.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +e: {I.has(I.tag(blk), r) == True{} : Bool}
  for ih: {I.has(I.tag(I.walk(I.tag(t), fix, blk, False{})), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, False{})), r) == True{} : Bool}

def has_blk.arm(k, h, t, r, fix, blk, e, ih):
  match k:
    case I.Other{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Star{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Lib{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Pkgs{}:
      has_cons(h, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Dir{}:
      has_right(fix, I.walk(I.tag(t), fix, blk, False{}), r, ih)
    case I.Allow{x}:
      has_left(blk, I.walk(I.tag(t), fix, blk, True{}), r, e)

# LAW: the walk puts the block down once, so what the block has, what the
# walk writes has
law has_blk:
  for raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +e: {I.has(I.tag(blk), r) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, blk, False{})), r) == True{} : Bool}

def has_blk(raw, r, fix, blk, e):
  match raw:
    case []:
      e
    case +h <> +t:
      has_blk.arm(I.kind(h), h, t, r, fix, blk, e, has_blk(t, r, fix, blk, e))

# LAW: a rule the walk keeps, which the file has or the rules put in, is in
# what the walk writes, with whether the file has it and whether it has a
# `.ez/` line given as parameters. A file with no `.ez/` line gets the rules
# in front of the block.
law has_rule.arm:
  for +raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +a: List<&2, String>
  for s: Bool
  for dd: Bool
  for es: {I.has(I.tag(raw), r) == s : Bool}
  for edd: {I.has(I.tag(raw), I.Dir{}) == dd : Bool}
  for +kr: {keeps(r) == True{} : Bool}
  for pr: {Bool.or(s, I.has(I.tag(fix), r)) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, List.append(&2, String, I.need(dd, fix), a),
    False{})), r) == True{} : Bool}

def has_rule.arm(raw, r, fix, a, s, dd, es, edd, kr, pr):
  match s dd:
    case True{} _:
      has_kept(raw, r, fix, List.append(&2, String, I.need(dd, fix), a), False{}, kr, es)
    case False{} True{}:
      has_dir(raw, r, fix, List.append(&2, String, I.need(True{}, fix), a), False{}, edd, pr)
    case False{} False{}:
      has_blk(raw, r, fix, List.append(&2, String, fix, a),
        has_left(fix, a, r, pr))

law has_rule:
  for +raw: List<&2, String>
  for +r: I.Rule
  for +fix: List<&2, String>
  for +a: List<&2, String>
  for +kr: {keeps(r) == True{} : Bool}
  for pr: {Bool.or(I.has(I.tag(raw), r), I.has(I.tag(fix), r)) == True{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix,
    List.append(&2, String, I.need(I.has(I.tag(raw), I.Dir{}), fix), a), False{})), r)
    == True{} : Bool}

def has_rule(raw, r, fix, a, kr, pr):
  has_rule.arm(raw, r, fix, a, I.has(I.tag(raw), r), I.has(I.tag(raw), I.Dir{}),
    {==}, {==}, kr, pr)

# LAW: the file has `.ez/*`, or the rules put it in
law rules_star:
  for s: Bool
  for l: Bool
  for p: Bool
  {Bool.or(s, I.has(I.tag(I.rules.go(s, l, p)), I.Star{})) == True{} : Bool}

def rules_star(s, l, p):
  match s l p:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: and `!.ez/lib`
law rules_lib:
  for s: Bool
  for l: Bool
  for p: Bool
  {Bool.or(l, I.has(I.tag(I.rules.go(s, l, p)), I.Lib{})) == True{} : Bool}

def rules_lib(s, l, p):
  match s l p:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: and `.ez/lib/*`
law rules_pkgs:
  for s: Bool
  for l: Bool
  for p: Bool
  {Bool.or(p, I.has(I.tag(I.rules.go(s, l, p)), I.Pkgs{})) == True{} : Bool}

def rules_pkgs(s, l, p):
  match s l p:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: the rules are none of them missing when all three are there
law rules_none:
  for a: Bool
  for b: Bool
  for c: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  for ec: {c == True{} : Bool}
  {I.rules.go(a, b, c) == [] : List<&2, String>}

def rules_none(a, b, c, ea, eb, ec):
  %Equal.sym(Bool, a, True{}, ea) : {I.rules.go(_, b, c) == [] : List<&2, String>}
  %Equal.sym(Bool, b, True{}, eb) : {I.rules.go(True{}, _, c) == [] : List<&2, String>}
  %Equal.sym(Bool, c, True{}, ec) : {I.rules.go(True{}, True{}, _) == [] : List<&2, String>}
  {==}

# LAW: the three rules are kept as they are, whichever of them are written
law rules_kept:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {kept.all(I.rules.go(b1, b2, b3)) == True{} : Bool}

def rules_kept(b1, b2, b3):
  match b1 b2 b3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: and none of them is `.ez/`
law rules_nodir:
  for b1: Bool
  for b2: Bool
  for b3: Bool
  {I.has(I.tag(I.rules.go(b1, b2, b3)), I.Dir{}) == False{} : Bool}

def rules_nodir(b1, b2, b3):
  match b1 b2 b3:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# LAW: the rules, written or not, are kept as they are
law need_kept:
  for s: Bool
  for +rs: List<&2, String>
  for h: {kept.all(rs) == True{} : Bool}
  {kept.all(I.need(s, rs)) == True{} : Bool}

def need_kept(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: and are not `.ez/`
law need_nodir:
  for s: Bool
  for +rs: List<&2, String>
  for h: {I.has(I.tag(rs), I.Dir{}) == False{} : Bool}
  {I.has(I.tag(I.need(s, rs)), I.Dir{}) == False{} : Bool}

def need_nodir(s, _rs, h):
  match s:
    case True{}:
      {==}
    case False{}:
      h

# LAW: the lines ez writes for hashes that name something are allowlist lines
law each_allowed:
  for +hs: List<&2, String>
  for +e: {full.all(hs) == True{} : Bool}
  {allowed.all(I.allow.each(hs)) == True{} : Bool}

def each_allowed(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(I.Rule, I.kind(I.allow(h)), I.Allow{h}, kind_allow(h, full_head(h, t, e)))
        : {Bool.and(allowed(_), allowed.all(I.allow.each(t))) == True{} : Bool}
      each_allowed(t, full_tail(h, t, e))

# LAW: and none of them is `.ez/`
law each_nodir:
  for +hs: List<&2, String>
  for +e: {full.all(hs) == True{} : Bool}
  {I.has(I.tag(I.allow.each(hs)), I.Dir{}) == False{} : Bool}

def each_nodir(hs, e):
  match hs:
    case []:
      {==}
    case +h <> +t:
      %Equal.sym(I.Rule, I.kind(I.allow(h)), I.Allow{h}, kind_allow(h, full_head(h, t, e)))
        : {I.has.step(I.same(_, I.Dir{}), _u => I.has(I.tag(I.allow.each(t)), I.Dir{}))
          == False{} : Bool}
      each_nodir(t, full_tail(h, t, e))

# LAW: the block, put down or not, has no `.ez/` line when it has none
law placed_nodir:
  for +d: Bool
  for +blk: List<&2, String>
  for hb: {I.has(I.tag(blk), I.Dir{}) == False{} : Bool}
  {I.has(I.tag(I.placed(d, blk)), I.Dir{}) == False{} : Bool}

def placed_nodir(d, _blk, hb):
  match d:
    case True{}:
      {==}
    case False{}:
      hb

# LAW: one line of the walk, with its kind given as a parameter: the walk
# writes no `.ez/` line when neither the rules nor the block has one
law has_nodir.arm:
  for k: I.Rule
  for +h: String
  for +t: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for ek: {I.kind(h) == k : I.Rule}
  for +hf: {I.has(I.tag(fix), I.Dir{}) == False{} : Bool}
  for +hb: {I.has(I.tag(blk), I.Dir{}) == False{} : Bool}
  for ihd: {I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{}) == False{} : Bool}
  for iht: {I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), I.Dir{}) == False{} : Bool}
  {I.has(I.tag(I.walk(I.Line{k, h} <> I.tag(t), fix, blk, d)), I.Dir{}) == False{} : Bool}

def has_nodir.arm(k, h, t, fix, blk, d, ek, hf, hb, ihd, iht):
  match k:
    case I.Other{}:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        I.has.step(I.same(I.Other{}, I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        Equal.cong(I.Rule, Bool,
          q => I.has.step(I.same(q, I.Dir{}),
            _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
          I.kind(h), I.Other{}, ek),
        ihd)
    case I.Star{}:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        I.has.step(I.same(I.Star{}, I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        Equal.cong(I.Rule, Bool,
          q => I.has.step(I.same(q, I.Dir{}),
            _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
          I.kind(h), I.Star{}, ek),
        ihd)
    case I.Lib{}:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        I.has.step(I.same(I.Lib{}, I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        Equal.cong(I.Rule, Bool,
          q => I.has.step(I.same(q, I.Dir{}),
            _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
          I.kind(h), I.Lib{}, ek),
        ihd)
    case I.Pkgs{}:
      Equal.trans(Bool,
        I.has.step(I.same(I.kind(h), I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        I.has.step(I.same(I.Pkgs{}, I.Dir{}),
          _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        Equal.cong(I.Rule, Bool,
          q => I.has.step(I.same(q, I.Dir{}),
            _u => I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
          I.kind(h), I.Pkgs{}, ek),
        ihd)
    case I.Dir{}:
      Equal.trans(Bool,
        I.has(I.tag(List.append(&2, String, fix, I.walk(I.tag(t), fix, blk, d))), I.Dir{}),
        Bool.or(I.has(I.tag(fix), I.Dir{}), I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{})),
        False{},
        has_app(fix, I.walk(I.tag(t), fix, blk, d), I.Dir{}),
        or_ff(I.has(I.tag(fix), I.Dir{}), I.has(I.tag(I.walk(I.tag(t), fix, blk, d)), I.Dir{}),
          hf, ihd))
    case I.Allow{x}:
      Equal.trans(Bool,
        I.has(I.tag(List.append(&2, String, I.placed(d, blk),
          I.walk(I.tag(t), fix, blk, True{}))), I.Dir{}),
        Bool.or(I.has(I.tag(I.placed(d, blk)), I.Dir{}),
          I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), I.Dir{})),
        False{},
        has_app(I.placed(d, blk), I.walk(I.tag(t), fix, blk, True{}), I.Dir{}),
        or_ff(I.has(I.tag(I.placed(d, blk)), I.Dir{}),
          I.has(I.tag(I.walk(I.tag(t), fix, blk, True{})), I.Dir{}),
          placed_nodir(d, blk, hb), iht))

# LAW: the walk writes no `.ez/` line when neither the rules nor the block
# has one: every `.ez/` line of the file is replaced
law has_nodir:
  for raw: List<&2, String>
  for +fix: List<&2, String>
  for +blk: List<&2, String>
  for +d: Bool
  for +hf: {I.has(I.tag(fix), I.Dir{}) == False{} : Bool}
  for +hb: {I.has(I.tag(blk), I.Dir{}) == False{} : Bool}
  {I.has(I.tag(I.walk(I.tag(raw), fix, blk, d)), I.Dir{}) == False{} : Bool}

def has_nodir(raw, fix, blk, d, hf, hb):
  match raw:
    case []:
      placed_nodir(d, blk, hb)
    case +h <> +t:
      has_nodir.arm(I.kind(h), h, t, fix, blk, d, {==}, hf, hb,
        has_nodir(t, fix, blk, d, hf, hb),
        has_nodir(t, fix, blk, True{}, hf, hb))

# the first run of the walk over a file, with the block it puts down. Law
# vocabulary: ez never calls it.
def one(+ls: List<&2, String>, blk: List<&2, String>) -> List<&2, String>:
  I.walk(I.tag(ls), I.rules(I.tag(ls)), blk, False{})

# the second run, over what the first wrote, with its own block: the rules
# the first run's output lacks, unless it has a `.ez/` line or `emp` says the
# ledger vends nothing, and then the allowlist lines `a`
def two(+ls: List<&2, String>, +blk: List<&2, String>, emp: Bool, a: List<&2, String>) -> List<&2, String>:
  +m = one(ls, blk)
  I.walk(I.tag(m), I.rules(I.tag(m)),
    List.append(&2, String, I.need(Bool.or(I.has(I.tag(m), I.Dir{}), emp), I.rules(I.tag(m))),
      a), False{})

# LAW: the second run over a first run that put no block down, whose own
# block is empty too, gives the first run's output back
law idem_none:
  for +ls: List<&2, String>
  {two(ls, [], True{}, []) == one(ls, []) : List<&2, String>}

def idem_none(ls):
  Equal.trans(List<&2, String>,
    two(ls, [], True{}, []),
    I.walk(I.tag(one(ls, [])), I.rules(I.tag(one(ls, []))), [], False{}),
    one(ls, []),
    Equal.cong(Bool, List<&2, String>,
      x => I.walk(I.tag(one(ls, [])), I.rules(I.tag(one(ls, []))),
        List.append(&2, String, I.need(x, I.rules(I.tag(one(ls, [])))), []), False{}),
      Bool.or(I.has(I.tag(one(ls, [])), I.Dir{}), True{}), True{},
      or_true(I.has(I.tag(one(ls, [])), I.Dir{}))),
    idem_nil(ls, I.rules(I.tag(ls)), I.rules(I.tag(one(ls, []))), False{}, False{},
      rules_kept(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))))

# LAW: what the first run writes over a ledger that vends a hash has no
# `.ez/` line
law one_nodir:
  for +ls: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +e: {full.all(a1 <> as) == True{} : Bool}
  {I.has(I.tag(one(ls, List.append(&2, String,
    I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
    I.Dir{}) == False{} : Bool}

def one_nodir(ls, a1, as, e):
  has_nodir(ls, I.rules(I.tag(ls)),
    List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow.each(a1 <> as)), False{},
    rules_nodir(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
      I.has(I.tag(ls), I.Pkgs{})),
    Equal.trans(Bool,
      I.has(I.tag(List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
        I.rules(I.tag(ls))), I.allow.each(a1 <> as))), I.Dir{}),
      Bool.or(I.has(I.tag(I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls)))), I.Dir{}),
        I.has(I.tag(I.allow.each(a1 <> as)), I.Dir{})),
      False{},
      has_app(I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
        I.allow.each(a1 <> as), I.Dir{}),
      or_ff(I.has(I.tag(I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls)))), I.Dir{}),
        I.has(I.tag(I.allow.each(a1 <> as)), I.Dir{}),
        need_nodir(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls)),
          rules_nodir(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
            I.has(I.tag(ls), I.Pkgs{}))),
        each_nodir(a1 <> as, e))))

# LAW: and lacks none of the three rules
law one_rules:
  for +ls: List<&2, String>
  for +a: List<&2, String>
  {I.rules(I.tag(one(ls, List.append(&2, String,
    I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), a)))) == [] : List<&2, String>}

def one_rules(ls, a):
  rules_none(
    I.has(I.tag(one(ls, List.append(&2, String,
      I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), a))), I.Star{}),
    I.has(I.tag(one(ls, List.append(&2, String,
      I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), a))), I.Lib{}),
    I.has(I.tag(one(ls, List.append(&2, String,
      I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), a))), I.Pkgs{}),
    has_rule(ls, I.Star{}, I.rules(I.tag(ls)), a, {==},
      rules_star(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))),
    has_rule(ls, I.Lib{}, I.rules(I.tag(ls)), a, {==},
      rules_lib(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))),
    has_rule(ls, I.Pkgs{}, I.rules(I.tag(ls)), a, {==},
      rules_pkgs(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{}))))

# LAW: the second run over a first run that put a block of hashes down gives
# the first run's output back: its own block is those hashes' lines, which
# go back where they were
law idem_some:
  for +ls: List<&2, String>
  for +a1: String
  for +as: List<&2, String>
  for +e: {full.all(a1 <> as) == True{} : Bool}
  {two(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
    I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as))
    == one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow.each(a1 <> as))) : List<&2, String>}

def idem_some(ls, a1, as, e):
  Equal.trans(List<&2, String>,
    two(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
    I.walk(I.tag(one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
      I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
      I.rules(I.tag(one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
        I.rules(I.tag(ls))), I.allow.each(a1 <> as))))),
      I.allow.each(a1 <> as), False{}),
    one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow.each(a1 <> as))),
    Equal.cong(List<&2, String>, List<&2, String>,
      y => I.walk(I.tag(one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
        I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
        I.rules(I.tag(one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
          I.rules(I.tag(ls))), I.allow.each(a1 <> as))))), y, False{}),
      List.append(&2, String,
        I.need(Bool.or(I.has(I.tag(one(ls, List.append(&2, String,
          I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
          I.Dir{}), False{}),
          I.rules(I.tag(one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))))),
        I.allow.each(a1 <> as)),
      I.allow.each(a1 <> as),
      Equal.trans(List<&2, String>,
        List.append(&2, String,
          I.need(Bool.or(I.has(I.tag(one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
            I.Dir{}), False{}),
            I.rules(I.tag(one(ls, List.append(&2, String,
              I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))))),
          I.allow.each(a1 <> as)),
        List.append(&2, String,
          I.rules(I.tag(one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as))))),
          I.allow.each(a1 <> as)),
        I.allow.each(a1 <> as),
        Equal.cong(Bool, List<&2, String>,
          x => List.append(&2, String,
            I.need(Bool.or(x, False{}),
              I.rules(I.tag(one(ls, List.append(&2, String,
                I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))))),
            I.allow.each(a1 <> as)),
          I.has(I.tag(one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as)))),
            I.Dir{}),
          False{}, one_nodir(ls, a1, as, e)),
        Equal.cong(List<&2, String>, List<&2, String>,
          y => List.append(&2, String, y, I.allow.each(a1 <> as)),
          I.rules(I.tag(one(ls, List.append(&2, String,
            I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))), I.allow.each(a1 <> as))))),
          [], one_rules(ls, I.allow.each(a1 <> as))))),
    idem_walk(ls, I.rules(I.tag(ls)), I.need(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls))),
      I.allow(a1), I.allow.each(as),
      I.rules(I.tag(one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
        I.rules(I.tag(ls))), I.allow.each(a1 <> as))))),
      rules_kept(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
        I.has(I.tag(ls), I.Pkgs{})),
      need_kept(I.has(I.tag(ls), I.Dir{}), I.rules(I.tag(ls)),
        rules_kept(I.has(I.tag(ls), I.Star{}), I.has(I.tag(ls), I.Lib{}),
          I.has(I.tag(ls), I.Pkgs{}))),
      each_allowed(a1 <> as, e)))

# LAW: `I.lines` run again on the lines it made, with the vendored hashes
# given as a parameter that names something at every hash
law lines_idem.arm:
  for +ls: List<&2, String>
  for v: List<&2, String>
  for +e: {full.all(v) == True{} : Bool}
  {two(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}),
    List.is_empty(&2, String, v)), I.rules(I.tag(ls))), I.allow.each(v)),
    List.is_empty(&2, String, v), I.allow.each(v))
    == one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}),
      List.is_empty(&2, String, v)), I.rules(I.tag(ls))), I.allow.each(v)))
    : List<&2, String>}

def lines_idem.arm(ls, v, e):
  match v:
    case []:
      Equal.trans(List<&2, String>,
        two(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), True{}),
          I.rules(I.tag(ls))), []), True{}, []),
        two(ls, [], True{}, []),
        one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), True{}),
          I.rules(I.tag(ls))), [])),
        Equal.cong(Bool, List<&2, String>,
          x => two(ls, List.append(&2, String, I.need(x, I.rules(I.tag(ls))), []), True{}, []),
          Bool.or(I.has(I.tag(ls), I.Dir{}), True{}), True{},
          or_true(I.has(I.tag(ls), I.Dir{}))),
        Equal.trans(List<&2, String>,
          two(ls, [], True{}, []),
          one(ls, []),
          one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), True{}),
            I.rules(I.tag(ls))), [])),
          idem_none(ls),
          Equal.cong(Bool, List<&2, String>,
            x => one(ls, List.append(&2, String, I.need(x, I.rules(I.tag(ls))), [])),
            True{}, Bool.or(I.has(I.tag(ls), I.Dir{}), True{}),
            Equal.sym(Bool, Bool.or(I.has(I.tag(ls), I.Dir{}), True{}), True{},
              or_true(I.has(I.tag(ls), I.Dir{}))))))
    case +a1 <> +as:
      Equal.trans(List<&2, String>,
        two(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
          I.rules(I.tag(ls))), I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
        two(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
          I.rules(I.tag(ls))), I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
        one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
          I.rules(I.tag(ls))), I.allow.each(a1 <> as))),
        Equal.cong(Bool, List<&2, String>,
          x => two(ls, List.append(&2, String, I.need(x, I.rules(I.tag(ls))),
            I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
          Bool.or(I.has(I.tag(ls), I.Dir{}), False{}), I.has(I.tag(ls), I.Dir{}),
          or_false(I.has(I.tag(ls), I.Dir{}))),
        Equal.trans(List<&2, String>,
          two(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
            I.rules(I.tag(ls))), I.allow.each(a1 <> as)), False{}, I.allow.each(a1 <> as)),
          one(ls, List.append(&2, String, I.need(I.has(I.tag(ls), I.Dir{}),
            I.rules(I.tag(ls))), I.allow.each(a1 <> as))),
          one(ls, List.append(&2, String, I.need(Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
            I.rules(I.tag(ls))), I.allow.each(a1 <> as))),
          idem_some(ls, a1, as, e),
          Equal.cong(Bool, List<&2, String>,
            x => one(ls, List.append(&2, String, I.need(x, I.rules(I.tag(ls))),
              I.allow.each(a1 <> as))),
            I.has(I.tag(ls), I.Dir{}), Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
            Equal.sym(Bool, Bool.or(I.has(I.tag(ls), I.Dir{}), False{}),
              I.has(I.tag(ls), I.Dir{}), or_false(I.has(I.tag(ls), I.Dir{}))))))

# LAW: `I.lines` run on the lines it made gives them back
law lines_idem:
  for +ds: List<&2, M.Dep>
  for +ls: List<&2, String>
  {I.lines(ds, I.lines(ds, ls)) == I.lines(ds, ls) : List<&2, String>}

def lines_idem(ds, ls):
  lines_idem.arm(ls, I.vended(ds), vended_full(ds))

# LAW: `sync` run on the file it wrote, with whether the first run changed
# the lines given as a parameter. An unchanged file was already in sync; a
# changed one reads back as the lines `I.lines` made, which it makes again.
law sync_idem.arm:
  for +ds: List<&2, M.Dep>
  for +text: String
  for b: Bool
  for eb: {String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
    I.file.text(I.file.lines(text))) == b : Bool}
  for +ev: {Str.clear.all(I.vended(ds), '\n') == True{} : Bool}
  {I.sync(ds, I.text.out(b, text, I.file.text(I.lines(ds, I.file.lines(text)))))
    == I.text.out(b, text, I.file.text(I.lines(ds, I.file.lines(text)))) : String}

def sync_idem.arm(ds, text, b, eb, ev):
  match b:
    case True{}:
      %Equal.sym(Bool, String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
        I.file.text(I.file.lines(text))), True{}, eb)
        : {I.text.out(_, text, I.file.text(I.lines(ds, I.file.lines(text)))) == text : String}
      {==}
    case False{}:
      %Equal.sym(List<&2, String>,
        I.file.lines(I.file.text(I.lines(ds, I.file.lines(text)))),
        I.lines(ds, I.file.lines(text)),
        file_lines_text(I.lines(ds, I.file.lines(text)),
          lines_clear(ds, I.file.lines(text), file_lines_clear(text), ev)))
        : {I.text.out(String.eq(I.file.text(I.lines(ds, _)), I.file.text(_)),
          I.file.text(I.lines(ds, I.file.lines(text))), I.file.text(I.lines(ds, _)))
          == I.file.text(I.lines(ds, I.file.lines(text))) : String}
      %Equal.sym(List<&2, String>, I.lines(ds, I.lines(ds, I.file.lines(text))),
        I.lines(ds, I.file.lines(text)), lines_idem(ds, I.file.lines(text)))
        : {I.text.out(String.eq(I.file.text(_),
          I.file.text(I.lines(ds, I.file.lines(text)))),
          I.file.text(I.lines(ds, I.file.lines(text))), I.file.text(_))
          == I.file.text(I.lines(ds, I.file.lines(text))) : String}
      %Equal.sym(Bool, String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
        I.file.text(I.lines(ds, I.file.lines(text)))), True{},
        Eq.string_eq_self(I.file.text(I.lines(ds, I.file.lines(text)))))
        : {I.text.out(_, I.file.text(I.lines(ds, I.file.lines(text))),
          I.file.text(I.lines(ds, I.file.lines(text))))
          == I.file.text(I.lines(ds, I.file.lines(text))) : String}
      {==}

def Laws.sync_idempotent(ds, text, ev):
  sync_idem.arm(ds, text,
    String.eq(I.file.text(I.lines(ds, I.file.lines(text))),
      I.file.text(I.file.lines(text))), {==}, ev)

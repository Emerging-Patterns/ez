# manifest: the proofs. `bend PROOF.bend` is the gate.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./manifest.bend as M
import ./render.bend as R
import ./ignore.bend as I
import ../check/eq.bend as Eq
import ./upgrade.bend as U
import ../check/str.bend as Str
import ../check/toml.bend as TP
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
    == M.Hub{""} : M.Source}
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
        c => M.find.pick(c, M.Dep{n, h, e, s}, M.Dep{"", "", "", M.Hub{""}}),
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
        case M.Hub{_named}:
          {==}
        case M.Git{url, rev, tag, root, nar, vend}:
          {==}
    case False{}:
      match s:
        case M.Hub{_named}:
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

def has_kept.cons.arm(b, h, _t, w, r, eb, e, ih):
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

# Import rewriting. The text is cut at its newlines and joined back, and no
# rewritten line holds a newline, so the lines afterwards are the lines
# before, each rewritten. A line that names no moved hash is left as it is.
# A line that names one is rewritten by the first move of it, and no move
# after that one names the new hash, since a hash holds no `/`: a line that
# starts `import <a>/` and `import <b>/` has `a` and `b` the same.

# LAW: the empty line names nothing, so a move leaves it
law line_empty:
  for +o: String
  for +n: String
  {U.reimport.line("", o, n) == "" : String}

def line_empty(o, _n):
  match o:
    case SNil{}:
      {==}
    case SCon{c, r}:
      {==}

# LAW: and so does every move
law many_empty:
  for ss: List<&2, U.Swap>
  {U.reimport.many.line(ss, "") == "" : String}

def many_empty(ss):
  match ss:
    case []:
      {==}
    case U.Swap{+o, +n} <> +t:
      Equal.trans(String,
        U.reimport.many.line(t, U.reimport.line("", o, n)),
        U.reimport.many.line(t, ""),
        "",
        Equal.cong(String, String, x => U.reimport.many.line(t, x),
          U.reimport.line("", o, n), "", line_empty(o, n)),
        many_empty(t))

# LAW: the line at a place, after every line was rewritten, is the line that
# was there, rewritten
law at_many:
  for +ss: List<&2, U.Swap>
  for ls: List<&2, String>
  for i: Nat
  {Laws.line.at(U.reimport.many.lines(ss, ls), i)
    == U.reimport.many.line(ss, Laws.line.at(ls, i)) : String}

def at_many(ss, ls, i):
  match ls i:
    case Nil{} _:
      Equal.sym(String, U.reimport.many.line(ss, ""), "", many_empty(ss))
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      at_many(ss, t, p)

# LAW: a line a move names starts with the text the move writes in front
law head_clear:
  for +n: String
  for +en: {Str.clear(n, '\n') == True{} : Bool}
  {Str.clear(U.reimport.head(n), '\n') == True{} : Bool}

def head_clear(n, en):
  Equal.trans(Bool,
    Str.clear(String.append(n, "/"), '\n'),
    Bool.and(Str.clear(n, '\n'), Str.clear("/", '\n')),
    True{},
    Str.clear_append_eq(n, "/", '\n'),
    and_tt(Str.clear(n, '\n'), Str.clear("/", '\n'), en, {==}))

# LAW: one line, with whether the move names it given as a parameter: what the
# move writes holds no newline when the line and the new hash hold none
law line_clear.arm:
  for b: Bool
  for +l: String
  for +o: String
  for +n: String
  for +el: {Str.clear(l, '\n') == True{} : Bool}
  for +en: {Str.clear(n, '\n') == True{} : Bool}
  {Str.clear(U.reimport.line.go(b, l, o, n), '\n') == True{} : Bool}

def line_clear.arm(b, l, o, n, el, en):
  match b:
    case True{}:
      Equal.trans(Bool,
        Str.clear(String.append(U.reimport.head(n),
          String.drop(l, String.length(U.reimport.head(o)))), '\n'),
        Bool.and(Str.clear(U.reimport.head(n), '\n'),
          Str.clear(String.drop(l, String.length(U.reimport.head(o))), '\n')),
        True{},
        Str.clear_append_eq(U.reimport.head(n),
          String.drop(l, String.length(U.reimport.head(o))), '\n'),
        and_tt(Str.clear(U.reimport.head(n), '\n'),
          Str.clear(String.drop(l, String.length(U.reimport.head(o))), '\n'),
          head_clear(n, en),
          Str.drop_clear(l, String.length(U.reimport.head(o)), '\n', el)))
    case False{}:
      el

# LAW: the old hash of the first move names something
law ok_old_full:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {Laws.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {String.is_empty(o) == False{} : Bool}

def ok_old_full(o, n, t, ok):
  Eq.not.true(String.is_empty(o),
    Eq.and.left(Bool.not(String.is_empty(o)), Laws.plain(o),
      Eq.and.left(Bool.and(Bool.not(String.is_empty(o)), Laws.plain(o)),
        Bool.and(Laws.plain(n), Laws.olds.miss(t, n)),
        Eq.and.left(Bool.and(Bool.and(Bool.not(String.is_empty(o)), Laws.plain(o)),
          Bool.and(Laws.plain(n), Laws.olds.miss(t, n))), Laws.moves.ok(t), ok))))

# LAW: and is plain
law ok_old_plain:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {Laws.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {Laws.plain(o) == True{} : Bool}

def ok_old_plain(o, n, t, ok):
  Eq.and.right(Bool.not(String.is_empty(o)), Laws.plain(o),
    Eq.and.left(Bool.and(Bool.not(String.is_empty(o)), Laws.plain(o)),
      Bool.and(Laws.plain(n), Laws.olds.miss(t, n)),
      Eq.and.left(Bool.and(Bool.and(Bool.not(String.is_empty(o)), Laws.plain(o)),
        Bool.and(Laws.plain(n), Laws.olds.miss(t, n))), Laws.moves.ok(t), ok)))

# LAW: the new hash is plain
law ok_new_plain:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {Laws.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {Laws.plain(n) == True{} : Bool}

def ok_new_plain(o, n, t, ok):
  Eq.and.left(Laws.plain(n), Laws.olds.miss(t, n),
    Eq.and.right(Bool.and(Bool.not(String.is_empty(o)), Laws.plain(o)),
      Bool.and(Laws.plain(n), Laws.olds.miss(t, n)),
      Eq.and.left(Bool.and(Bool.and(Bool.not(String.is_empty(o)), Laws.plain(o)),
        Bool.and(Laws.plain(n), Laws.olds.miss(t, n))), Laws.moves.ok(t), ok)))

# LAW: and is no old hash of a move after it
law ok_new_miss:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {Laws.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {Laws.olds.miss(t, n) == True{} : Bool}

def ok_new_miss(o, n, t, ok):
  Eq.and.right(Laws.plain(n), Laws.olds.miss(t, n),
    Eq.and.right(Bool.and(Bool.not(String.is_empty(o)), Laws.plain(o)),
      Bool.and(Laws.plain(n), Laws.olds.miss(t, n)),
      Eq.and.left(Bool.and(Bool.and(Bool.not(String.is_empty(o)), Laws.plain(o)),
        Bool.and(Laws.plain(n), Laws.olds.miss(t, n))), Laws.moves.ok(t), ok)))

# LAW: and the moves after the first are an upgrade's moves too
law ok_rest:
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +ok: {Laws.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  {Laws.moves.ok(t) == True{} : Bool}

def ok_rest(o, n, t, ok):
  Eq.and.right(Bool.and(Bool.and(Bool.not(String.is_empty(o)), Laws.plain(o)),
    Bool.and(Laws.plain(n), Laws.olds.miss(t, n))), Laws.moves.ok(t), ok)

# LAW: a plain hash holds no `/`
law plain_slash:
  for +s: String
  for e: {Laws.plain(s) == True{} : Bool}
  {Str.clear(s, '/') == True{} : Bool}

def plain_slash(s, e):
  Eq.and.left(Str.clear(s, '/'), Str.clear(s, '\n'), e)

# LAW: and no newline
law plain_nl:
  for +s: String
  for e: {Laws.plain(s) == True{} : Bool}
  {Str.clear(s, '\n') == True{} : Bool}

def plain_nl(s, e):
  Eq.and.right(Str.clear(s, '/'), Str.clear(s, '\n'), e)

# LAW: a line put through every move holds no newline when it held none
law many_line_clear:
  for +ss: List<&2, U.Swap>
  for +l: String
  for +ok: {Laws.moves.ok(ss) == True{} : Bool}
  for +el: {Str.clear(l, '\n') == True{} : Bool}
  {Str.clear(U.reimport.many.line(ss, l), '\n') == True{} : Bool}

def many_line_clear(ss, l, ok, el):
  match ss:
    case []:
      el
    case U.Swap{+o, +n} <> +t:
      many_line_clear(t, U.reimport.line(l, o, n), ok_rest(o, n, t, ok),
        line_clear.arm(U.reimport.hit(String.is_empty(o), l, o), l, o, n, el,
          plain_nl(n, ok_new_plain(o, n, t, ok))))

# LAW: and so does every line
law many_lines_clear:
  for +ss: List<&2, U.Swap>
  for ls: List<&2, String>
  for +ok: {Laws.moves.ok(ss) == True{} : Bool}
  for +el: {Str.clear.all(ls, '\n') == True{} : Bool}
  {Str.clear.all(U.reimport.many.lines(ss, ls), '\n') == True{} : Bool}

def many_lines_clear(ss, ls, ok, el):
  match ls:
    case []:
      {==}
    case +h <> +t:
      and_tt(Str.clear(U.reimport.many.line(ss, h), '\n'),
        Str.clear.all(U.reimport.many.lines(ss, t), '\n'),
        many_line_clear(ss, h, ok, Eq.and.left(Str.clear(h, '\n'), Str.clear.all(t, '\n'), el)),
        many_lines_clear(ss, t, ok, Eq.and.right(Str.clear(h, '\n'), Str.clear.all(t, '\n'), el)))

# LAW: the pieces of a text, rewritten and joined back, cut back into those
# rewritten pieces
law by_line.arm:
  for +ss: List<&2, U.Swap>
  for +ps: List<&2, String>
  for +ok: {Laws.moves.ok(ss) == True{} : Bool}
  for +ec: {Str.clear.all(ps, '\n') == True{} : Bool}
  for ne: {List.is_empty(&2, String, ps) == False{} : Bool}
  {String.split(String.join(U.reimport.many.lines(ss, ps), "\n"), '\n')
    == U.reimport.many.lines(ss, ps) : List<&2, String>}

def by_line.arm(ss, ps, ok, ec, ne):
  match ps:
    case []:
      Eq.bit.absurd2(&2, {String.split(String.join(U.reimport.many.lines(ss, []), "\n"), '\n')
        == U.reimport.many.lines(ss, []) : List<&2, String>}, ne)
    case +p <> +r:
      Str.split_join(U.reimport.many.line(ss, p), U.reimport.many.lines(ss, r), '\n',
        many_lines_clear(ss, p <> r, ok, ec))

def Laws.rewrite_by_line(ss, text, ok):
  by_line.arm(ss, String.split(text, '\n'), ok, Str.split_clear(text, '\n'),
    Str.split_cons(text, '\n'))

# LAW: one move, with whether it can name anything given as a parameter,
# leaves a line that does not start with its `import <old>/`
law line_keeps.arm:
  for b: Bool
  for +l: String
  for +o: String
  for +n: String
  for e: {String.starts_with(l, U.reimport.head(o)) == False{} : Bool}
  {U.reimport.line.go(U.reimport.hit(b, l, o), l, o, n) == l : String}

def line_keeps.arm(b, l, o, n, e):
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, String.starts_with(l, U.reimport.head(o)), False{}, e)
        : {U.reimport.line.go(_, l, o, n) == l : String}
      {==}

# LAW: a line a move does not name is left as it is
law line_keeps:
  for +l: String
  for +o: String
  for +n: String
  for e: {String.starts_with(l, U.reimport.head(o)) == False{} : Bool}
  {U.reimport.line(l, o, n) == l : String}

def line_keeps(l, o, n, e):
  line_keeps.arm(String.is_empty(o), l, o, n, e)

# LAW: and a line no move names is left by all of them
law many_keeps:
  for ss: List<&2, U.Swap>
  for +l: String
  for +none: {Laws.names.none(ss, l) == True{} : Bool}
  {U.reimport.many.line(ss, l) == l : String}

def many_keeps(ss, l, none):
  match ss:
    case []:
      {==}
    case U.Swap{+o, +n} <> +t:
      Equal.trans(String,
        U.reimport.many.line(t, U.reimport.line(l, o, n)),
        U.reimport.many.line(t, l),
        l,
        Equal.cong(String, String, x => U.reimport.many.line(t, x),
          U.reimport.line(l, o, n), l,
          line_keeps(l, o, n, Eq.not.true(String.starts_with(l, U.reimport.head(o)),
            Eq.and.left(Bool.not(String.starts_with(l, U.reimport.head(o))),
              Laws.names.none(t, l), none)))),
        many_keeps(t, l, Eq.and.right(Bool.not(String.starts_with(l, U.reimport.head(o))),
          Laws.names.none(t, l), none)))

def Laws.rewrite_keeps_other_lines(ss, text, i, ok, miss):
  Equal.trans(String,
    Laws.line.at(String.lines(U.reimport.many(ss, text)), i),
    Laws.line.at(U.reimport.many.lines(ss, String.lines(text)), i),
    Laws.line.at(String.lines(text), i),
    Equal.cong(List<&2, String>, String, ls => Laws.line.at(ls, i),
      String.lines(U.reimport.many(ss, text)),
      U.reimport.many.lines(ss, String.lines(text)),
      Laws.rewrite_by_line(ss, text, ok)),
    Equal.trans(String,
      Laws.line.at(U.reimport.many.lines(ss, String.lines(text)), i),
      U.reimport.many.line(ss, Laws.line.at(String.lines(text), i)),
      Laws.line.at(String.lines(text), i),
      at_many(ss, String.lines(text), i),
      many_keeps(ss, Laws.line.at(String.lines(text), i), miss)))

# LAW: rewriting every line keeps their number
law many_length:
  for +ss: List<&2, U.Swap>
  for ls: List<&2, String>
  {List.length(&2, String, U.reimport.many.lines(ss, ls))
    == List.length(&2, String, ls) : Nat}

def many_length(ss, ls):
  match ls:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(Nat, Nat, x => 1n+x,
        List.length(&2, String, U.reimport.many.lines(ss, t)),
        List.length(&2, String, t), many_length(ss, t))

def Laws.rewrite_keeps_line_count(ss, text, ok):
  Equal.trans(Nat,
    List.length(&2, String, String.lines(U.reimport.many(ss, text))),
    List.length(&2, String, U.reimport.many.lines(ss, String.lines(text))),
    List.length(&2, String, String.lines(text)),
    Equal.cong(List<&2, String>, Nat, ls => List.length(&2, String, ls),
      String.lines(U.reimport.many(ss, text)),
      U.reimport.many.lines(ss, String.lines(text)),
      Laws.rewrite_by_line(ss, text, ok)),
    many_length(ss, String.lines(text)))

# LAW: lines none of which a move names are left as they are
law many_lines_keep:
  for +ss: List<&2, U.Swap>
  for ls: List<&2, String>
  for +none: {Laws.names.none.all(ss, ls) == True{} : Bool}
  {U.reimport.many.lines(ss, ls) == ls : List<&2, String>}

def many_lines_keep(ss, ls, none):
  match ls:
    case []:
      {==}
    case +h <> +t:
      Equal.trans(List<&2, String>,
        U.reimport.many.line(ss, h) <> U.reimport.many.lines(ss, t),
        h <> U.reimport.many.lines(ss, t),
        h <> t,
        Equal.cong(String, List<&2, String>, x => x <> U.reimport.many.lines(ss, t),
          U.reimport.many.line(ss, h), h,
          many_keeps(ss, h, Eq.and.left(Laws.names.none(ss, h), Laws.names.none.all(ss, t),
            none))),
        Equal.cong(List<&2, String>, List<&2, String>, y => h <> y,
          U.reimport.many.lines(ss, t), t,
          many_lines_keep(ss, t, Eq.and.right(Laws.names.none(ss, h),
            Laws.names.none.all(ss, t), none))))

def Laws.rewrite_nothing_named(ss, text, none):
  Equal.trans(String,
    String.join(U.reimport.many.lines(ss, String.split(text, '\n')), "\n"),
    String.join(String.split(text, '\n'), "\n"),
    text,
    Equal.cong(List<&2, String>, String, ls => String.join(ls, "\n"),
      U.reimport.many.lines(ss, String.split(text, '\n')), String.split(text, '\n'),
      many_lines_keep(ss, String.split(text, '\n'), none)),
    Str.join_split(text, '\n'))

# A line names one hash at most. `import <a>/` and `import <b>/` both at the
# front of a line, with neither hash holding `/`, have `a` and `b` the same:
# the first `/` after `import ` ends both.

# LAW: a prefix check that held had heads that compared equal
law sw_if_head:
  for t: String
  for p: String
  for s: Bool
  for e: {String.starts_with.if(t, p, s) == True{} : Bool}
  {s == True{} : Bool}

def sw_if_head(_t, _p, s, e):
  match s:
    case True{}:
      {==}
    case False{}:
      e

# LAW: and tails that held
law sw_if_tail:
  for t: String
  for p: String
  for s: Bool
  for e: {String.starts_with.if(t, p, s) == True{} : Bool}
  {String.starts_with(t, p) == True{} : Bool}

def sw_if_tail(t, p, s, e):
  match s:
    case True{}:
      e
    case False{}:
      Eq.bit.absurd(&2, {String.starts_with(t, p) == True{} : Bool}, e)

# LAW: a string that starts with two joined starts, past the first, with the
# second
law sw_drop:
  for p: String
  for +x: String
  for +q: String
  for e: {String.starts_with(x, String.append(p, q)) == True{} : Bool}
  {String.starts_with(String.drop(x, String.length(p)), q) == True{} : Bool}

def sw_drop(p, x, q, e):
  match p x:
    case SNil{} SNil{}:
      e
    case SNil{} SCon{y, r}:
      e
    case SCon{c, p2} SNil{}:
      Eq.bit.absurd(&2, {String.starts_with(String.drop(SNil{}, String.length(SCon{c, p2})), q)
        == True{} : Bool}, e)
    case SCon{+c, +p2} SCon{+y, +r}:
      sw_drop(p2, r, q, sw_if_tail(r, String.append(p2, q), Char.is_eq(y, c), e))

# LAW: `/` held by a string that holds none is a contradiction
law slash_clash:
  for +c: Char
  for +y: Char
  for +b: String
  for ey: {Char.is_eq(y, '/') == True{} : Bool}
  for ec: {Char.is_eq(y, c) == True{} : Bool}
  for eb: {Str.clear(SCon{c, b}, '/') == True{} : Bool}
  Empty

def slash_clash(c, y, b, ey, ec, eb):
  Eq.bit.clash2(Equal.trans(Bool, True{}, Char.is_eq(c, '/'), False{},
    Equal.trans(Bool, True{}, Char.is_eq(y, '/'), Char.is_eq(c, '/'),
      Equal.sym(Bool, Char.is_eq(y, '/'), True{}, ey),
      Equal.cong(Char, Bool, x => Char.is_eq(x, '/'), y, c, Str.char_eq_true(y, c, ec))),
    Eq.not.true(Char.is_eq(c, '/'),
      Eq.and.left(Bool.not(Char.is_eq(c, '/')), Str.clear(b, '/'), eb))))

# LAW: two strings that hold no `/`, each followed by `/` at the front of one
# text, are one string
law sl_same:
  for +a: String
  for +b: String
  for +z: String
  for +ea: {Str.clear(a, '/') == True{} : Bool}
  for +eb: {Str.clear(b, '/') == True{} : Bool}
  for +ha: {String.starts_with(z, String.append(a, "/")) == True{} : Bool}
  for +hb: {String.starts_with(z, String.append(b, "/")) == True{} : Bool}
  {a == b : String}

def sl_same(a, b, z, ea, eb, ha, hb):
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{+d, +b2}:
      match z:
        case SNil{}:
          Eq.bit.absurd(&2, {SNil{} == SCon{d, b2} : String}, ha)
        case SCon{+y, +r}:
          Empty.absurd({SNil{} == SCon{d, b2} : String},
            slash_clash(d, y, b2,
              sw_if_head(r, "", Char.is_eq(y, '/'), ha),
              sw_if_head(r, String.append(b2, "/"), Char.is_eq(y, d), hb), eb))
    case SCon{+c, +a2} SNil{}:
      match z:
        case SNil{}:
          Eq.bit.absurd(&2, {SCon{c, a2} == SNil{} : String}, ha)
        case SCon{+y, +r}:
          Empty.absurd({SCon{c, a2} == SNil{} : String},
            slash_clash(c, y, a2,
              sw_if_head(r, "", Char.is_eq(y, '/'), hb),
              sw_if_head(r, String.append(a2, "/"), Char.is_eq(y, c), ha), ea))
    case SCon{+c, +a2} SCon{+d, +b2}:
      match z:
        case SNil{}:
          Eq.bit.absurd(&2, {SCon{c, a2} == SCon{d, b2} : String}, ha)
        case SCon{+y, +r}:
          Equal.trans(String, SCon{c, a2}, SCon{d, a2}, SCon{d, b2},
            Equal.cong(Char, String, x => SCon{x, a2}, c, d,
              Equal.trans(Char, c, y, d,
                Equal.sym(Char, y, c, Str.char_eq_true(y, c,
                  sw_if_head(r, String.append(a2, "/"), Char.is_eq(y, c), ha))),
                Str.char_eq_true(y, d,
                  sw_if_head(r, String.append(b2, "/"), Char.is_eq(y, d), hb)))),
            Equal.cong(String, String, x => SCon{d, x}, a2, b2,
              sl_same(a2, b2, r,
                Eq.and.right(Bool.not(Char.is_eq(c, '/')), Str.clear(a2, '/'), ea),
                Eq.and.right(Bool.not(Char.is_eq(d, '/')), Str.clear(b2, '/'), eb),
                sw_if_tail(r, String.append(a2, "/"), Char.is_eq(y, c), ha),
                sw_if_tail(r, String.append(b2, "/"), Char.is_eq(y, d), hb))))

# LAW: a line that names two hashes that hold no `/` names one hash twice
law prefix_same:
  for +x: String
  for +a: String
  for +b: String
  for +ea: {Str.clear(a, '/') == True{} : Bool}
  for +eb: {Str.clear(b, '/') == True{} : Bool}
  for ha: {String.starts_with(x, U.reimport.head(a)) == True{} : Bool}
  for hb: {String.starts_with(x, U.reimport.head(b)) == True{} : Bool}
  {a == b : String}

def prefix_same(x, a, b, ea, eb, ha, hb):
  sl_same(a, b, String.drop(x, 7n), ea, eb,
    sw_drop("import ", x, String.append(a, "/"), ha),
    sw_drop("import ", x, String.append(b, "/"), hb))

# LAW: a line that names a plain hash names no plain hash the hash is not
law prefix_other:
  for +x: String
  for +a: String
  for +b: String
  for +ea: {Str.clear(a, '/') == True{} : Bool}
  for +eb: {Str.clear(b, '/') == True{} : Bool}
  for ha: {String.starts_with(x, U.reimport.head(a)) == True{} : Bool}
  for ne: {String.eq(b, a) == False{} : Bool}
  {String.starts_with(x, U.reimport.head(b)) == False{} : Bool}

# LAW: the same, with how the line compares to the second given as a
# parameter
law prefix_other.arm:
  for +x: String
  for +a: String
  for +b: String
  for s: Bool
  for es: {String.starts_with(x, U.reimport.head(b)) == s : Bool}
  for +ea: {Str.clear(a, '/') == True{} : Bool}
  for +eb: {Str.clear(b, '/') == True{} : Bool}
  for ha: {String.starts_with(x, U.reimport.head(a)) == True{} : Bool}
  for ne: {String.eq(b, a) == False{} : Bool}
  {String.starts_with(x, U.reimport.head(b)) == False{} : Bool}

def prefix_other.arm(x, a, b, s, es, ea, eb, ha, ne):
  match s:
    case False{}:
      es
    case True{}:
      Eq.bit.absurd2(&2, {String.starts_with(x, U.reimport.head(b)) == False{} : Bool},
        Equal.trans(Bool, True{}, String.eq(b, a), False{},
          Equal.trans(Bool, True{}, String.eq(b, b), String.eq(b, a),
            Equal.sym(Bool, String.eq(b, b), True{}, Eq.string_eq_self(b)),
            Equal.cong(String, Bool, q => String.eq(b, q), b, a,
              prefix_same(x, b, a, eb, ea, es, ha))),
          ne))

def prefix_other(x, a, b, ea, eb, ha, ne):
  prefix_other.arm(x, a, b, String.starts_with(x, U.reimport.head(b)), {==}, ea, eb, ha, ne)

# LAW: a line a move rewrote names none of the moves after it, whose old
# hashes are plain and none of which is the new hash
law names_none_new:
  for +t: List<&2, U.Swap>
  for +n: String
  for +rest: String
  for +pn: {Str.clear(n, '/') == True{} : Bool}
  for +miss: {Laws.olds.miss(t, n) == True{} : Bool}
  for +ok: {Laws.moves.ok(t) == True{} : Bool}
  {Laws.names.none(t, String.append(U.reimport.head(n), rest)) == True{} : Bool}

def names_none_new(t, n, rest, pn, miss, ok):
  match t:
    case []:
      {==}
    case U.Swap{+o, +n2} <> +t2:
      and_tt(Bool.not(String.starts_with(String.append(U.reimport.head(n), rest),
          U.reimport.head(o))),
        Laws.names.none(t2, String.append(U.reimport.head(n), rest)),
        not_of_false(String.starts_with(String.append(U.reimport.head(n), rest),
            U.reimport.head(o)),
          prefix_other(String.append(U.reimport.head(n), rest), n, o, pn,
            plain_slash(o, ok_old_plain(o, n2, t2, ok)),
            Eq.starts_append(U.reimport.head(n), rest),
            Eq.not.true(String.eq(o, n),
              Eq.and.left(Bool.not(String.eq(o, n)), Laws.olds.miss(t2, n), miss)))),
        names_none_new(t2, n, rest, pn,
          Eq.and.right(Bool.not(String.eq(o, n)), Laws.olds.miss(t2, n), miss),
          ok_rest(o, n2, t2, ok)))

# the hash a move sends to, or "" for none. Law vocabulary: ez never calls it.
def some.of(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{x}:
      x

# the type that is empty where a move was found
def some.emp(m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

# LAW: no move is found in no moves
law none_some:
  for +new: String
  for e: {None{} == Some{new} : Maybe<&2, String>}
  Empty

def none_some(_new, e):
  %e : some.emp(_)
  Unit{}

# LAW: a line a move names, when the move's old hash names something, is
# rewritten to start with the new hash
law line_hits:
  for +l: String
  for +o: String
  for +n: String
  for eo: {String.is_empty(o) == False{} : Bool}
  for eh: {String.starts_with(l, U.reimport.head(o)) == True{} : Bool}
  {U.reimport.line(l, o, n)
    == String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))
    : String}

def line_hits(l, o, n, eo, eh):
  %Equal.sym(Bool, String.is_empty(o), False{}, eo)
    : {U.reimport.line.go(U.reimport.hit(_, l, o), l, o, n)
      == String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))
      : String}
  %Equal.sym(Bool, String.starts_with(l, U.reimport.head(o)), True{}, eh)
    : {U.reimport.line.go(_, l, o, n)
      == String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))
      : String}
  {==}

# LAW: one move, with whether it is the first move of the old hash given as a
# parameter: the first rewrites the line, and no move after it touches it
# again; one of another hash does not name the line, which is left for the
# moves after it
law names_new.arm:
  for c: Bool
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +l: String
  for +old: String
  for +new: String
  for ec: {String.eq(o, old) == c : Bool}
  for +ok: {Laws.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  for to: {Bool.pick(Maybe<&2, String>, c, Some{n}, Laws.moved.to(t, old)) == Some{new}
    : Maybe<&2, String>}
  for +hit: {String.starts_with(l, U.reimport.head(old)) == True{} : Bool}
  for +pold: {Str.clear(old, '/') == True{} : Bool}
  for ih: {Laws.moved.to(t, old) == Some{new} : Maybe<&2, String>}
    -> {String.starts_with(U.reimport.many.line(t, l), U.reimport.head(new)) == True{} : Bool}
  {String.starts_with(U.reimport.many.line(t, U.reimport.line(l, o, n)),
    U.reimport.head(new)) == True{} : Bool}

def names_new.arm(c, o, n, t, l, old, new, ec, ok, to, hit, pold, ih):
  match c:
    case True{}:
      %Equal.cong(Maybe<&2, String>, String, m => some.of(m), Some{n}, Some{new}, to)
        : {String.starts_with(U.reimport.many.line(t, U.reimport.line(l, o, n)),
          U.reimport.head(_)) == True{} : Bool}
      %Equal.sym(String, U.reimport.line(l, o, n),
        String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o)))),
        line_hits(l, o, n, ok_old_full(o, n, t, ok),
          Equal.trans(Bool, String.starts_with(l, U.reimport.head(o)),
            String.starts_with(l, U.reimport.head(old)), True{},
            Equal.cong(String, Bool, q => String.starts_with(l, U.reimport.head(q)), o, old,
              Str.string_eq_true(o, old, ec)),
            hit)))
        : {String.starts_with(U.reimport.many.line(t, _), U.reimport.head(n)) == True{} : Bool}
      %Equal.sym(String,
        U.reimport.many.line(t,
          String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))),
        String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o)))),
        many_keeps(t,
          String.append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o)))),
          names_none_new(t, n, String.drop(l, String.length(U.reimport.head(o))),
            plain_slash(n, ok_new_plain(o, n, t, ok)), ok_new_miss(o, n, t, ok),
            ok_rest(o, n, t, ok))))
        : {String.starts_with(_, U.reimport.head(n)) == True{} : Bool}
      Eq.starts_append(U.reimport.head(n), String.drop(l, String.length(U.reimport.head(o))))
    case False{}:
      %Equal.sym(String, U.reimport.line(l, o, n), l,
        line_keeps(l, o, n,
          prefix_other(l, old, o, pold, plain_slash(o, ok_old_plain(o, n, t, ok)), hit, ec)))
        : {String.starts_with(U.reimport.many.line(t, _), U.reimport.head(new)) == True{} : Bool}
      ih(to)

# LAW: a line that names an old hash starts, after every move, with the hash
# the first move of it sends it to
law names_new:
  for ss: List<&2, U.Swap>
  for +l: String
  for +old: String
  for +new: String
  for +ok: {Laws.moves.ok(ss) == True{} : Bool}
  for to: {Laws.moved.to(ss, old) == Some{new} : Maybe<&2, String>}
  for +hit: {String.starts_with(l, U.reimport.head(old)) == True{} : Bool}
  for +pold: {Str.clear(old, '/') == True{} : Bool}
  {String.starts_with(U.reimport.many.line(ss, l), U.reimport.head(new)) == True{} : Bool}

def names_new(ss, l, old, new, ok, to, hit, pold):
  match ss:
    case []:
      Empty.absurd({String.starts_with(l, U.reimport.head(new)) == True{} : Bool},
        none_some(new, to))
    case U.Swap{+o, +n} <> +t:
      names_new.arm(String.eq(o, old), o, n, t, l, old, new, {==}, ok, to, hit, pold,
        x => names_new(t, l, old, new, ok_rest(o, n, t, ok), x, hit, pold))

# LAW: a hash a move is found for is plain, as every old hash of the moves is
law moved_plain.arm:
  for c: Bool
  for +o: String
  for +n: String
  for +t: List<&2, U.Swap>
  for +old: String
  for +new: String
  for ec: {String.eq(o, old) == c : Bool}
  for +ok: {Laws.moves.ok(U.Swap{o, n} <> t) == True{} : Bool}
  for to: {Bool.pick(Maybe<&2, String>, c, Some{n}, Laws.moved.to(t, old)) == Some{new}
    : Maybe<&2, String>}
  for ih: {Laws.moved.to(t, old) == Some{new} : Maybe<&2, String>}
    -> {Str.clear(old, '/') == True{} : Bool}
  {Str.clear(old, '/') == True{} : Bool}

def moved_plain.arm(c, o, n, t, old, _new, ec, ok, to, ih):
  match c:
    case True{}:
      %Str.string_eq_true(o, old, ec) : {Str.clear(_, '/') == True{} : Bool}
      plain_slash(o, ok_old_plain(o, n, t, ok))
    case False{}:
      ih(to)

law moved_plain:
  for ss: List<&2, U.Swap>
  for +old: String
  for +new: String
  for +ok: {Laws.moves.ok(ss) == True{} : Bool}
  for to: {Laws.moved.to(ss, old) == Some{new} : Maybe<&2, String>}
  {Str.clear(old, '/') == True{} : Bool}

def moved_plain(ss, old, new, ok, to):
  match ss:
    case []:
      Empty.absurd({Str.clear(old, '/') == True{} : Bool}, none_some(new, to))
    case U.Swap{+o, +n} <> +t:
      moved_plain.arm(String.eq(o, old), o, n, t, old, new, {==}, ok, to,
        x => moved_plain(t, old, new, ok_rest(o, n, t, ok), x))

def Laws.rewrite_names_new(ss, text, i, old, new, ok, to, hit):
  Equal.trans(Bool,
    String.starts_with(Laws.line.at(String.lines(U.reimport.many(ss, text)), i),
      U.reimport.head(new)),
    String.starts_with(U.reimport.many.line(ss, Laws.line.at(String.lines(text), i)),
      U.reimport.head(new)),
    True{},
    Equal.trans(Bool,
      String.starts_with(Laws.line.at(String.lines(U.reimport.many(ss, text)), i),
        U.reimport.head(new)),
      String.starts_with(Laws.line.at(U.reimport.many.lines(ss, String.lines(text)), i),
        U.reimport.head(new)),
      String.starts_with(U.reimport.many.line(ss, Laws.line.at(String.lines(text), i)),
        U.reimport.head(new)),
      Equal.cong(List<&2, String>, Bool,
        ls => String.starts_with(Laws.line.at(ls, i), U.reimport.head(new)),
        String.lines(U.reimport.many(ss, text)),
        U.reimport.many.lines(ss, String.lines(text)),
        Laws.rewrite_by_line(ss, text, ok)),
      Equal.cong(String, Bool, x => String.starts_with(x, U.reimport.head(new)),
        Laws.line.at(U.reimport.many.lines(ss, String.lines(text)), i),
        U.reimport.many.line(ss, Laws.line.at(String.lines(text), i)),
        at_many(ss, String.lines(text), i))),
    names_new(ss, Laws.line.at(String.lines(text), i), old, new, ok, to, hit,
      moved_plain(ss, old, new, ok, to)))

# ---------------------------------------------------------------------------
# EZ-LED-5: a `[tools.*]` section is judged at its own head, where its name
# does not start `deps.`, and every section before it is passed over the same
# way on both sides, so each law is an induction over the sections before it.

def Laws.tool_section_not_dep(ss1, n, ps, ss2):
  match ss1:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, M.Dep>, List<&2, M.Dep>,
        x => M.deps.put(String.starts_with(M.name_of(h), "deps."), h, x),
        M.deps(List.append(&2, T.Sect, t, T.Sect{"tools." ++ n, ps} <> ss2)),
        M.deps(List.append(&2, T.Sect, t, ss2)),
        Laws.tool_section_not_dep(t, n, ps, ss2))

# LAW: a section filed ahead of two lists of tools is filed ahead of the first
law tools_put_append:
  for b: Bool
  for +h: T.Sect
  for xs: List<&2, M.Tool>
  for +ys: List<&2, M.Tool>
  {M.tools.put(b, h, List.append(&2, M.Tool, xs, ys))
    == List.append(&2, M.Tool, M.tools.put(b, h, xs), ys) : List<&2, M.Tool>}

def tools_put_append(b, h, _xs, _ys):
  match b:
    case True{}:
      match h:
        case T.Sect{_n, _ps}:
          {==}
    case False{}:
      {==}

def Laws.tool_section_is_tool(ss1, n, ps, ss2):
  match ss1:
    case []:
      %Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
        : {M.tools.put(_, T.Sect{"tools." ++ n, ps}, M.tools(ss2))
          == M.tool_of("tools." ++ n, ps) <> M.tools(ss2) : List<&2, M.Tool>}
      {==}
    case +h <> +t:
      Equal.trans(List<&2, M.Tool>,
        M.tools.put(String.starts_with(M.name_of(h), "tools."), h,
          M.tools(List.append(&2, T.Sect, t, T.Sect{"tools." ++ n, ps} <> ss2))),
        M.tools.put(String.starts_with(M.name_of(h), "tools."), h,
          List.append(&2, M.Tool, M.tools(t), M.tool_of("tools." ++ n, ps) <> M.tools(ss2))),
        List.append(&2, M.Tool,
          M.tools.put(String.starts_with(M.name_of(h), "tools."), h, M.tools(t)),
          M.tool_of("tools." ++ n, ps) <> M.tools(ss2)),
        Equal.cong(List<&2, M.Tool>, List<&2, M.Tool>,
          x => M.tools.put(String.starts_with(M.name_of(h), "tools."), h, x),
          M.tools(List.append(&2, T.Sect, t, T.Sect{"tools." ++ n, ps} <> ss2)),
          List.append(&2, M.Tool, M.tools(t), M.tool_of("tools." ++ n, ps) <> M.tools(ss2)),
          Laws.tool_section_is_tool(t, n, ps, ss2)),
        tools_put_append(String.starts_with(M.name_of(h), "tools."), h, M.tools(t),
          M.tool_of("tools." ++ n, ps) <> M.tools(ss2)))

def Laws.tool_needs_no_hash(ss1, n, ps, ss2):
  match ss1:
    case []:
      {==}
    case +h <> +t:
      Equal.cong(String, String,
        x => M.missing.at(M.missing.is(h), M.name_of(h), x),
        M.missing(List.append(&2, T.Sect, t, T.Sect{"tools." ++ n, ps} <> ss2)),
        M.missing(List.append(&2, T.Sect, t, ss2)),
        Laws.tool_needs_no_hash(t, n, ps, ss2))

# ---------------------------------------------------------------------------
# EZ-LED-4: a ledger ez renders parses back to the model it was rendered from.
# The proof has the shape of the lock's (EZ-DOC-1, lock/PROOF.bend). First the
# text: the renderer writes the lines of a document of tables (`show_text`),
# each table its header and the rows that have a value, and eztoml v0.1.0 cuts
# the text back into those lines and reads them into the tables
# (`ledger_sections_read`), as check/toml.bend's `sections_read` does for a
# document eztoml itself renders. The ledger's one difference is `vendor =
# true`, written bare, which a row of its own carries (`step_vendor`). Then
# the model: `M.build` finds in the tables the fields they were written from
# (`read_ledger`), since every row with no value was left out and every key is
# written once in its table (`value_keep`). `R.renderable` is what makes both
# halves hold.

# a line of a rendered ledger: a key with its value quoted, or a key with its
# value written bare, as `vendor = true` is. Proof vocabulary.
type Row is Data:
  Q{key: String, val: String}
  B{key: String, val: String}

def row.key(r: Row) -> String:
  match r:
    case Q{k, _v}:
      k
    case B{k, _v}:
      k

def row.val(r: Row) -> String:
  match r:
    case Q{_k, v}:
      v
    case B{_k, v}:
      v

# the pair a row reads back as
def row.kv(r: Row) -> T.Kv:
  match r:
    case Q{k, v}:
      T.Kv{k, v}
    case B{k, v}:
      T.Kv{k, v}

# the row's line, without its newline
def row.line(r: Row) -> String:
  match r:
    case Q{k, v}:
      TP.pair.line(T.Kv{k, v})
    case B{k, v}:
      k ++ " = " ++ v

# the row as the renderer writes it: nothing when its value is empty
def row.text(r: Row) -> String:
  match r:
    case Q{k, v}:
      R.line(k, v)
    case B{k, v}:
      R.line.bare(k, v)

# whether a row reads back as its pair: a quoted row's key is bare and holds
# no `=`, `"` or newline, and its value no newline; a bare row is `vendor =
# true`, or has no value and so is not written
def row.ok(r: Row) -> Bool:
  match r:
    case Q{+k, +v}:
      Bool.and(T.bare(k), Bool.and(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
        Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')))))
    case B{+k, +v}:
      Bool.or(String.is_empty(v), Bool.and(String.eq(k, "vendor"), String.eq(v, "true")))

def rows.ok(rs: List<&2, Row>) -> Bool:
  match rs:
    case []:
      True{}
    case h <> t:
      rest = rows.ok(t)
      Bool.and(row.ok(h), rest)

# a row kept ahead of the rest, or dropped when its value is empty
def keep.put(empty: Bool, r: Row, rest: List<&2, Row>) -> List<&2, Row>:
  match empty:
    case True{}:
      rest
    case False{}:
      r <> rest

# the rows that are written: those with a value
def keep(rs: List<&2, Row>) -> List<&2, Row>:
  match rs:
    case []:
      []
    case +r <> t:
      keep.put(String.is_empty(row.val(r)), r, keep(t))

# the pairs a table being filled holds once a row is read, kept or dropped
def keep.acc(empty: Bool, r: Row, acc: List<&2, T.Kv>) -> List<&2, T.Kv>:
  match empty:
    case True{}:
      acc
    case False{}:
      row.kv(r) <> acc

def rows.lines(rs: List<&2, Row>) -> List<&2, String>:
  match rs:
    case []:
      []
    case h <> t:
      row.line(h) <> rows.lines(t)

def rows.kvs(rs: List<&2, Row>) -> List<&2, T.Kv>:
  match rs:
    case []:
      []
    case h <> t:
      row.kv(h) <> rows.kvs(t)

def rows.text(rs: List<&2, Row>) -> String:
  match rs:
    case []:
      ""
    case h <> t:
      row.text(h) ++ rows.text(t)

# LAW: the one bare line a ledger holds, read into a table being filled, adds
# its pair
law step_vendor:
  for bad: String
  for +n: String
  for acc: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for en: {String.is_empty(n) == False{} : Bool}
  {T.step(T.Toml{bad, n, acc, done}, "vendor = true")
    == T.Toml{bad, n, T.Kv{"vendor", "true"} <> acc, done} : T.Toml}

def step_vendor(bad, n, acc, done, en):
  %Equal.sym(Bool, String.is_empty(n), False{}, en)
    : {T.put.go(_, bad, n, acc, done, "vendor", "true")
      == T.Toml{bad, n, T.Kv{"vendor", "true"} <> acc, done} : T.Toml}
  {==}

# LAW: a row with a value, read into a table being filled, adds its pair
law step_row:
  for bad: String
  for +n: String
  for acc: List<&2, T.Kv>
  for done: List<&2, T.Sect>
  for +r: Row
  for en: {String.is_empty(n) == False{} : Bool}
  for ev: {String.is_empty(row.val(r)) == False{} : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  {T.step(T.Toml{bad, n, acc, done}, row.line(r))
    == T.Toml{bad, n, row.kv(r) <> acc, done} : T.Toml}

def step_row(bad, n, acc, done, r, en, ev, ok):
  match r:
    case Q{+k, +v}:
      +ok2 = Eq.and.right(T.bare(k), Bool.and(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
        Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')))), ok)
      TP.step_pair(bad, n, acc, done, k, v, en,
        Eq.and.left(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
          Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))), ok2),
        Eq.and.left(Str.clear(k, '"'), Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')),
          Eq.and.right(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
            Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))), ok2)))
    case B{+k, +v}:
      +ab = Equal.trans(Bool, Bool.and(String.eq(k, "vendor"), String.eq(v, "true")),
        Bool.or(String.is_empty(v), Bool.and(String.eq(k, "vendor"), String.eq(v, "true"))),
        True{},
        Equal.cong(Bool, Bool, x => Bool.or(x, Bool.and(String.eq(k, "vendor"), String.eq(v, "true"))),
          False{}, String.is_empty(v), Equal.sym(Bool, String.is_empty(v), False{}, ev)),
        ok)
      ek = Str.string_eq_true(k, "vendor", Eq.and.left(String.eq(k, "vendor"), String.eq(v, "true"), ab))
      evv = Str.string_eq_true(v, "true", Eq.and.right(String.eq(k, "vendor"), String.eq(v, "true"), ab))
      %Equal.sym(String, k, "vendor", ek) : {T.step(T.Toml{bad, n, acc, done}, _ ++ " = " ++ v)
        == T.Toml{bad, n, T.Kv{_, v} <> acc, done} : T.Toml}
      %Equal.sym(String, v, "true", evv) : {T.step(T.Toml{bad, n, acc, done}, "vendor = " ++ _)
        == T.Toml{bad, n, T.Kv{"vendor", _} <> acc, done} : T.Toml}
      step_vendor(bad, n, acc, done, en)


# LAW: one row, kept or dropped, read into a table being filled, with whether
# its value is empty given as a parameter
law walk_rows.arm:
  for +r: Row
  for +t: List<&2, Row>
  for +rest: List<&2, String>
  for +bad: String
  for +n: String
  for +acc: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for b: Bool
  for eb: {String.is_empty(row.val(r)) == b : Bool}
  for +en: {String.is_empty(n) == False{} : Bool}
  for +ok: {row.ok(r) == True{} : Bool}
  for ih: {T.parse.walk(List.append(&2, String, rows.lines(keep(t)), rest),
      T.Toml{bad, n, keep.acc(b, r, acc), done})
    == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(t)),
      keep.acc(b, r, acc)), done}) : T.Toml}
  {T.parse.walk(List.append(&2, String, rows.lines(keep.put(b, r, keep(t))), rest),
      T.Toml{bad, n, acc, done})
    == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv,
      rows.kvs(keep.put(b, r, keep(t))), acc), done}) : T.Toml}

def walk_rows.arm(r, t, rest, bad, n, acc, done, b, eb, en, ok, ih):
  match b:
    case True{}:
      ih
    case False{}:
      s = Equal.sym(T.Toml, T.step(T.Toml{bad, n, acc, done}, row.line(r)),
        T.Toml{bad, n, row.kv(r) <> acc, done},
        step_row(bad, n, acc, done, r, en, eb, ok))
      %s : {T.parse.walk(List.append(&2, String, rows.lines(keep(t)), rest), _)
        == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv,
          rows.kvs(keep(t)), row.kv(r) <> acc), done}) : T.Toml}
      ih

# LAW: the rows a table writes, read into it, add their pairs, reversed
law walk_rows:
  for +rs: List<&2, Row>
  for +rest: List<&2, String>
  for +bad: String
  for +n: String
  for +acc: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +en: {String.is_empty(n) == False{} : Bool}
  for +eok: {rows.ok(rs) == True{} : Bool}
  {T.parse.walk(List.append(&2, String, rows.lines(keep(rs)), rest), T.Toml{bad, n, acc, done})
    == T.parse.walk(rest, T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), acc), done})
    : T.Toml}

# by induction on the rows, each one kept or dropped
def walk_rows(rs, rest, bad, n, acc, done, en, eok):
  match rs:
    case []:
      {==}
    case +r <> +t:
      walk_rows.arm(r, t, rest, bad, n, acc, done, String.is_empty(row.val(r)), {==}, en,
        Eq.and.left(row.ok(r), rows.ok(t), eok),
        walk_rows(t, rest, bad, n, keep.acc(String.is_empty(row.val(r)), r, acc), done, en,
          Eq.and.right(row.ok(r), rows.ok(t), eok)))

# a table of a rendered ledger: its name and every row it may write. Proof
# vocabulary.
type RSect is Data:
  RSect{name: String, rows: List<&2, Row>}

# the lines of a ledger: each table's header, the rows it writes, and a blank
# line
def rdoc.lines(ss: List<&2, RSect>) -> List<&2, String>:
  match ss:
    case []:
      []
    case RSect{n, rs} <> t:
      TP.head.line(n) <> List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t))

# the table a table of rows reads back as
def sect.of(s: RSect) -> T.Sect:
  RSect{n, rs} = s
  T.Sect{n, rows.kvs(keep(rs))}

def sects.of(ss: List<&2, RSect>) -> List<&2, T.Sect>:
  match ss:
    case []:
      []
    case h <> t:
      sect.of(h) <> sects.of(t)

# whether a table reads back: its name is not empty and holds no newline, and
# every row reads back
def rsect.ok(s: RSect) -> Bool:
  RSect{+n, rs} = s
  Bool.and(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), rows.ok(rs)))

def rsects.ok(ss: List<&2, RSect>) -> Bool:
  match ss:
    case []:
      True{}
    case h <> t:
      rest = rsects.ok(t)
      Bool.and(rsect.ok(h), rest)

# LAW: a table's lines, read, fill it and file the one before it
law walk_rsect:
  for +n: String
  for +rs: List<&2, Row>
  for +t: List<&2, RSect>
  for +bad: String
  for +name: String
  for +pairs: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +en: {String.is_empty(n) == False{} : Bool}
  for +eok: {rows.ok(rs) == True{} : Bool}
  {T.parse.walk(rdoc.lines(RSect{n, rs} <> t), T.Toml{bad, name, pairs, done})
    == T.parse.walk(rdoc.lines(t),
      T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done)})
    : T.Toml}

# the header, then the rows; the blank line changes nothing
def walk_rsect(n, rs, t, bad, name, pairs, done, en, eok):
  h = Equal.sym(T.Toml, T.step(T.Toml{bad, name, pairs, done}, TP.head.line(n)),
    T.Toml{bad, n, [], T.flush(name, pairs, done)}, TP.step_head(bad, name, pairs, done, n))
  %h : {T.parse.walk(List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t)), _)
    == T.parse.walk(rdoc.lines(t),
      T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done)})
    : T.Toml}
  walk_rows(rs, "" <> rdoc.lines(t), bad, n, [], T.flush(name, pairs, done), en, eok)

# LAW: a ledger's lines, read from any state with no error, file the tables
# it already filed and then every table the ledger holds
law walk_rdoc:
  for +ss: List<&2, RSect>
  for +bad: String
  for +name: String
  for +pairs: List<&2, T.Kv>
  for +done: List<&2, T.Sect>
  for +eok: {rsects.ok(ss) == True{} : Bool}
  {T.parse.fin(T.parse.walk(rdoc.lines(ss), T.Toml{bad, name, pairs, done}))
    == T.Toml{bad, "", [], List.append(&2, T.Sect,
      List.reverse(&2, T.Sect, T.flush(name, pairs, done)), sects.of(ss))} : T.Toml}

# by induction on the tables
def walk_rdoc(ss, bad, name, pairs, done, eok):
  match ss:
    case []:
      Equal.cong(List<&2, T.Sect>, T.Toml, x => T.Toml{bad, "", [], x},
        List.reverse(&2, T.Sect, T.flush(name, pairs, done)),
        List.append(&2, T.Sect, List.reverse(&2, T.Sect, T.flush(name, pairs, done)), []),
        Equal.sym(List<&2, T.Sect>,
          List.append(&2, T.Sect, List.reverse(&2, T.Sect, T.flush(name, pairs, done)), []),
          List.reverse(&2, T.Sect, T.flush(name, pairs, done)),
          Str.list_append_nil(T.Sect, List.reverse(&2, T.Sect, T.flush(name, pairs, done)))))
    case RSect{+n, +rs} <> +t:
      +ok = Eq.and.left(rsect.ok(RSect{n, rs}), rsects.ok(t), eok)
      +en = Eq.not.true(String.is_empty(n), Eq.and.left(Bool.not(String.is_empty(n)),
        Bool.and(Str.clear(n, '\n'), rows.ok(rs)), ok))
      ep = Eq.and.right(Str.clear(n, '\n'), rows.ok(rs),
        Eq.and.right(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), rows.ok(rs)), ok))
      w = Equal.sym(T.Toml,
        T.parse.walk(rdoc.lines(RSect{n, rs} <> t), T.Toml{bad, name, pairs, done}),
        T.parse.walk(rdoc.lines(t),
          T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done)}),
        walk_rsect(n, rs, t, bad, name, pairs, done, en, ep))
      %w : {T.parse.fin(_) == T.Toml{bad, "", [], List.append(&2, T.Sect,
        List.reverse(&2, T.Sect, T.flush(name, pairs, done)), sects.of(RSect{n, rs} <> t))} : T.Toml}
      Equal.trans(T.Toml,
        T.parse.fin(T.parse.walk(rdoc.lines(t),
          T.Toml{bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done)})),
        T.Toml{bad, "", [], List.append(&2, T.Sect, List.reverse(&2, T.Sect,
          T.flush(n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done))),
          sects.of(t))},
        T.Toml{bad, "", [], List.append(&2, T.Sect,
          List.reverse(&2, T.Sect, T.flush(name, pairs, done)), sects.of(RSect{n, rs} <> t))},
        walk_rdoc(t, bad, n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []),
          T.flush(name, pairs, done), Eq.and.right(rsect.ok(RSect{n, rs}), rsects.ok(t), eok)),
        Equal.cong(List<&2, T.Sect>, T.Toml, x => T.Toml{bad, "", [], x},
          List.append(&2, T.Sect, List.reverse(&2, T.Sect,
            T.flush(n, List.reverse.go(&2, T.Kv, rows.kvs(keep(rs)), []), T.flush(name, pairs, done))),
            sects.of(t)),
          List.append(&2, T.Sect,
            List.reverse(&2, T.Sect, T.flush(name, pairs, done)), sects.of(RSect{n, rs} <> t)),
          TP.flush_filed(n, rows.kvs(keep(rs)), T.flush(name, pairs, done), sects.of(t), en)))

# LAW: a bare row with a value that reads back is `vendor = true`
law vendor_row:
  for +k: String
  for +v: String
  for ev: {String.is_empty(v) == False{} : Bool}
  for ok: {Bool.or(String.is_empty(v), Bool.and(String.eq(k, "vendor"), String.eq(v, "true")))
    == True{} : Bool}
  {B{k, v} == B{"vendor", "true"} : Row}

# the `or`'s first half is False, so its second answered True
def vendor_row(k, v, ev, ok):
  +ab = Equal.trans(Bool, Bool.and(String.eq(k, "vendor"), String.eq(v, "true")),
    Bool.or(String.is_empty(v), Bool.and(String.eq(k, "vendor"), String.eq(v, "true"))),
    True{},
    Equal.cong(Bool, Bool, x => Bool.or(x, Bool.and(String.eq(k, "vendor"), String.eq(v, "true"))),
      False{}, String.is_empty(v), Equal.sym(Bool, String.is_empty(v), False{}, ev)),
    ok)
  ek = Str.string_eq_true(k, "vendor", Eq.and.left(String.eq(k, "vendor"), String.eq(v, "true"), ab))
  evv = Str.string_eq_true(v, "true", Eq.and.right(String.eq(k, "vendor"), String.eq(v, "true"), ab))
  %Equal.sym(String, k, "vendor", ek) : {B{_, v} == B{"vendor", "true"} : Row}
  %Equal.sym(String, v, "true", evv) : {B{"vendor", _} == B{"vendor", "true"} : Row}
  {==}

# LAW: a row with a value that reads back writes a line with no newline
law row_clear:
  for +r: Row
  for ev: {String.is_empty(row.val(r)) == False{} : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  {Str.clear(row.line(r), '\n') == True{} : Bool}

def row_clear(r, ev, ok):
  match r:
    case Q{+k, +v}:
      +ok3 = Eq.and.right(Str.clear(k, '"'), Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')),
        Eq.and.right(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
          Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n'))),
          Eq.and.right(T.bare(k), Bool.and(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
            Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')))), ok)))
      Str.clear_append(T.key(k), " = " ++ T.quote(v), '\n',
        TP.key_clear.go(k, T.bare(k), Eq.and.left(Str.clear(k, '\n'), Str.clear(v, '\n'), ok3)),
        Str.clear_append(v, "\"", '\n',
          Eq.and.right(Str.clear(k, '\n'), Str.clear(v, '\n'), ok3), {==}))
    case B{+k, +v}:
      %Equal.sym(Row, B{k, v}, B{"vendor", "true"}, vendor_row(k, v, ev, ok))
        : {Str.clear(row.line(_), '\n') == True{} : Bool}
      {==}

# LAW: one row, kept or dropped, with whether its value is empty given
law rows_clear.arm:
  for +r: Row
  for +t: List<&2, Row>
  for b: Bool
  for eb: {String.is_empty(row.val(r)) == b : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  for ih: {Str.clear.all(rows.lines(keep(t)), '\n') == True{} : Bool}
  {Str.clear.all(rows.lines(keep.put(b, r, keep(t))), '\n') == True{} : Bool}

def rows_clear.arm(r, t, b, eb, ok, ih):
  match b:
    case True{}:
      ih
    case False{}:
      Str.and_true(Str.clear(row.line(r), '\n'), Str.clear.all(rows.lines(keep(t)), '\n'),
        row_clear(r, eb, ok), ih)

# LAW: no line a table's rows write holds a newline
law rows_clear:
  for +rs: List<&2, Row>
  for +eok: {rows.ok(rs) == True{} : Bool}
  {Str.clear.all(rows.lines(keep(rs)), '\n') == True{} : Bool}

def rows_clear(rs, eok):
  match rs:
    case []:
      {==}
    case +r <> +t:
      rows_clear.arm(r, t, String.is_empty(row.val(r)), {==},
        Eq.and.left(row.ok(r), rows.ok(t), eok),
        rows_clear(t, Eq.and.right(row.ok(r), rows.ok(t), eok)))

# LAW: no line of a ledger that reads back holds a newline
law rlines_clear:
  for +ss: List<&2, RSect>
  for +eok: {rsects.ok(ss) == True{} : Bool}
  {Str.clear.all(rdoc.lines(ss), '\n') == True{} : Bool}

# by induction on the tables
def rlines_clear(ss, eok):
  match ss:
    case []:
      {==}
    case RSect{+n, +rs} <> +t:
      +ok = Eq.and.right(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), rows.ok(rs)),
        Eq.and.left(rsect.ok(RSect{n, rs}), rsects.ok(t), eok))
      Str.and_true(Str.clear(TP.head.line(n), '\n'),
        Str.clear.all(List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t)), '\n'),
        Str.clear_append(n, "]", '\n', Eq.and.left(Str.clear(n, '\n'), rows.ok(rs), ok), {==}),
        Str.clear_all_append(rows.lines(keep(rs)), "" <> rdoc.lines(t), '\n',
          rows_clear(rs, Eq.and.right(Str.clear(n, '\n'), rows.ok(rs), ok)),
          rlines_clear(t, Eq.and.right(rsect.ok(RSect{n, rs}), rsects.ok(t), eok))))

# LAW: parsing a ledger's lines joined by newlines gives back its tables, and
# no error, when every table reads back and there is at least one
law rsections_read:
  for +s: RSect
  for +t: List<&2, RSect>
  for +eok: {rsects.ok(s <> t) == True{} : Bool}
  {T.parse(String.join(rdoc.lines(s <> t), "\n")) == T.Toml{"", "", [], sects.of(s <> t)}
    : T.Toml}

# the text is the lines joined, which cut back into the lines
def rsections_read(s, t, eok):
  match s:
    case RSect{+n, +rs}:
      sp = Equal.sym(List<&2, String>,
        String.split(String.join(rdoc.lines(RSect{n, rs} <> t), "\n"), '\n'),
        rdoc.lines(RSect{n, rs} <> t),
        Str.split_join(TP.head.line(n),
          List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t)), '\n',
          rlines_clear(RSect{n, rs} <> t, eok)))
      %sp : {T.parse.fin(T.parse.walk(_, T.Toml{"", "", [], []}))
        == T.Toml{"", "", [], sects.of(RSect{n, rs} <> t)} : T.Toml}
      walk_rdoc(RSect{n, rs} <> t, "", "", [], [], eok)

# ---------------------------------------------------------------------------
# the renderer's text as lines

# LAW: a row with no value writes nothing
law text_empty:
  for +r: Row
  for eb: {String.is_empty(row.val(r)) == True{} : Bool}
  {row.text(r) == "" : String}

def text_empty(r, eb):
  match r:
    case Q{k, +v}:
      %Equal.sym(Bool, String.is_empty(v), True{}, eb)
        : {Bool.pick(String, _, "", k ++ " = \"" ++ v ++ "\"\n") == "" : String}
      {==}
    case B{k, +v}:
      %Equal.sym(Bool, String.is_empty(v), True{}, eb)
        : {Bool.pick(String, _, "", k ++ " = " ++ v ++ "\n") == "" : String}
      {==}

# LAW: a quoted row with a value writes its line and a newline, ahead of
# whatever follows
law text_line.q:
  for +k: String
  for +v: String
  for +x: String
  for ev: {String.is_empty(v) == False{} : Bool}
  for ek: {T.bare(k) == True{} : Bool}
  {String.append(row.line(Q{k, v}), SCon{'\n', x}) == String.append(row.text(Q{k, v}), x)
    : String}

def text_line.q(k, v, x, ev, ek):
  %Equal.sym(Bool, String.is_empty(v), False{}, ev)
    : {String.append(row.line(Q{k, v}), SCon{'\n', x})
      == String.append(Bool.pick(String, _, "", k ++ " = \"" ++ v ++ "\"\n"), x) : String}
  %Equal.sym(Bool, T.bare(k), True{}, ek)
    : {String.append(String.append(Bool.pick(String, _, k, T.quote(k)), " = " ++ T.quote(v)),
        SCon{'\n', x})
      == String.append(k ++ " = \"" ++ v ++ "\"\n", x) : String}
  a1 = Equal.sym(String, String.append(String.append(k, " = " ++ T.quote(v)), SCon{'\n', x}),
    String.append(k, String.append(" = " ++ T.quote(v), SCon{'\n', x})),
    Eq.append_assoc(k, " = " ++ T.quote(v), SCon{'\n', x}))
  %a1 : {_ == String.append(k ++ " = \"" ++ v ++ "\"\n", x) : String}
  a2 = Equal.sym(String, String.append(k ++ " = \"" ++ v ++ "\"\n", x),
    String.append(k, String.append(" = \"" ++ v ++ "\"\n", x)),
    Eq.append_assoc(k, " = \"" ++ v ++ "\"\n", x))
  %a2 : {String.append(k, String.append(" = " ++ T.quote(v), SCon{'\n', x})) == _ : String}
  a3 = Equal.sym(String, String.append(String.append(v, "\""), SCon{'\n', x}),
    String.append(v, String.append("\"", SCon{'\n', x})),
    Eq.append_assoc(v, "\"", SCon{'\n', x}))
  %a3 : {String.append(k, " = \"" ++ _)
    == String.append(k, String.append(" = \"" ++ v ++ "\"\n", x)) : String}
  a4 = Equal.sym(String, String.append(String.append(v, "\"\n"), x),
    String.append(v, String.append("\"\n", x)),
    Eq.append_assoc(v, "\"\n", x))
  %a4 : {String.append(k, " = \"" ++ String.append(v, String.append("\"", SCon{'\n', x})))
    == String.append(k, " = \"" ++ _) : String}
  {==}

# LAW: a row with a value that reads back writes its line and a newline,
# ahead of whatever follows
law text_line:
  for +r: Row
  for +x: String
  for ev: {String.is_empty(row.val(r)) == False{} : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  {String.append(row.line(r), SCon{'\n', x}) == String.append(row.text(r), x) : String}

def text_line(r, x, ev, ok):
  match r:
    case Q{+k, +v}:
      text_line.q(k, v, x, ev,
        Eq.and.left(T.bare(k), Bool.and(Str.clear(k, '='), Bool.and(Str.clear(k, '"'),
          Bool.and(Str.clear(k, '\n'), Str.clear(v, '\n')))), ok))
    case B{+k, +v}:
      %Equal.sym(Row, B{k, v}, B{"vendor", "true"}, vendor_row(k, v, ev, ok))
        : {String.append(row.line(_), SCon{'\n', x}) == String.append(row.text(_), x) : String}
      {==}

# LAW: one row, kept or dropped, written, with whether its value is empty given
law rows_text.arm:
  for +r: Row
  for +t: List<&2, Row>
  for b: Bool
  for eb: {String.is_empty(row.val(r)) == b : Bool}
  for ok: {row.ok(r) == True{} : Bool}
  for ih: {TP.unlines(rows.lines(keep(t))) == rows.text(t) : String}
  {TP.unlines(rows.lines(keep.put(b, r, keep(t)))) == String.append(row.text(r), rows.text(t))
    : String}

def rows_text.arm(r, t, b, eb, ok, ih):
  match b:
    case True{}:
      %Equal.sym(String, row.text(r), "", text_empty(r, eb))
        : {TP.unlines(rows.lines(keep(t))) == String.append(_, rows.text(t)) : String}
      ih
    case False{}:
      %Equal.sym(String, TP.unlines(rows.lines(keep(t))), rows.text(t), ih)
        : {String.append(row.line(r), SCon{'\n', _})
          == String.append(row.text(r), rows.text(t)) : String}
      text_line(r, rows.text(t), eb, ok)

# LAW: the lines a table's rows write, each ended by a newline, are the text
# the renderer writes for them
law rows_text:
  for +rs: List<&2, Row>
  for +eok: {rows.ok(rs) == True{} : Bool}
  {TP.unlines(rows.lines(keep(rs))) == rows.text(rs) : String}

def rows_text(rs, eok):
  match rs:
    case []:
      {==}
    case +r <> +t:
      rows_text.arm(r, t, String.is_empty(row.val(r)), {==},
        Eq.and.left(row.ok(r), rows.ok(t), eok),
        rows_text(t, Eq.and.right(row.ok(r), rows.ok(t), eok)))

# rows written ahead of a text. Proof vocabulary.
def rows.cat(rs: List<&2, Row>, x: String) -> String:
  match rs:
    case []:
      x
    case h <> t:
      String.append(row.text(h), rows.cat(t, x))

# LAW: rows written ahead of a text are their text, then it
law rows_cat:
  for +rs: List<&2, Row>
  for +x: String
  {rows.cat(rs, x) == String.append(rows.text(rs), x) : String}

def rows_cat(rs, x):
  match rs:
    case []:
      {==}
    case +r <> +t:
      %Equal.sym(String, rows.cat(t, x), String.append(rows.text(t), x), rows_cat(t, x))
        : {String.append(row.text(r), _)
          == String.append(String.append(row.text(r), rows.text(t)), x) : String}
      Equal.sym(String, String.append(String.append(row.text(r), rows.text(t)), x),
        String.append(row.text(r), String.append(rows.text(t), x)),
        Eq.append_assoc(row.text(r), rows.text(t), x))

# LAW: and two lists of rows are the first ahead of the second
law rows_cat_append:
  for +as: List<&2, Row>
  for +bs: List<&2, Row>
  for +x: String
  {rows.cat(List.append(&2, Row, as, bs), x) == rows.cat(as, rows.cat(bs, x)) : String}

def rows_cat_append(as, bs, x):
  match as:
    case []:
      {==}
    case +r <> +t:
      Equal.cong(String, String, y => String.append(row.text(r), y),
        rows.cat(List.append(&2, Row, t, bs), x), rows.cat(t, rows.cat(bs, x)),
        rows_cat_append(t, bs, x))

# LAW: a section's header and rows as the renderer writes them, a blank line
# first, ahead of whatever follows, are that blank line and the section's
# lines, when the rows' text is what the lines give
law blk_text:
  for +p: String
  for +n: String
  for +z: String
  for +u: String
  for +x: String
  for e: {String.append(u, x) == String.append(z, x) : String}
  {String.append(SCon{'\n', SCon{'[', String.append(p, String.append(n, SCon{']', SCon{'\n', z}}))}}, x)
    == SCon{'\n', String.append(String.append(SCon{'[', String.append(String.append(p, n), "]")},
      SCon{'\n', u}), x)} : String}

def blk_text(p, n, z, u, x, e):
  l1 = Eq.append_assoc(p, String.append(n, SCon{']', SCon{'\n', z}}), x)
  l2 = Equal.cong(String, String, y => String.append(p, y),
    String.append(String.append(n, SCon{']', SCon{'\n', z}}), x),
    String.append(n, SCon{']', SCon{'\n', String.append(z, x)}}),
    Eq.append_assoc(n, SCon{']', SCon{'\n', z}}, x))
  l3 = Equal.cong(String, String, y => String.append(p, String.append(n, SCon{']', SCon{'\n', y}})),
    String.append(z, x), String.append(u, x), Equal.sym(String, String.append(u, x), String.append(z, x), e))
  r1 = Eq.append_assoc(String.append(String.append(p, n), "]"), SCon{'\n', u}, x)
  r2 = Eq.append_assoc(String.append(p, n), "]", SCon{'\n', String.append(u, x)})
  r3 = Eq.append_assoc(p, n, SCon{']', SCon{'\n', String.append(u, x)}})
  Equal.cong(String, String, y => SCon{'\n', SCon{'[', y}},
    String.append(String.append(p, String.append(n, SCon{']', SCon{'\n', z}})), x),
    String.append(String.append(String.append(String.append(p, n), "]"), SCon{'\n', u}), x),
    Equal.trans(String,
      String.append(String.append(p, String.append(n, SCon{']', SCon{'\n', z}})), x),
      String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
      String.append(String.append(String.append(String.append(p, n), "]"), SCon{'\n', u}), x),
      Equal.trans(String,
        String.append(String.append(p, String.append(n, SCon{']', SCon{'\n', z}})), x),
        String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(z, x)}})),
        String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
        Equal.trans(String,
          String.append(String.append(p, String.append(n, SCon{']', SCon{'\n', z}})), x),
          String.append(p, String.append(String.append(n, SCon{']', SCon{'\n', z}}), x)),
          String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(z, x)}})),
          l1, l2),
        l3),
      Equal.sym(String,
        String.append(String.append(String.append(String.append(p, n), "]"), SCon{'\n', u}), x),
        String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
        Equal.trans(String,
          String.append(String.append(String.append(String.append(p, n), "]"), SCon{'\n', u}), x),
          String.append(String.append(String.append(p, n), "]"), SCon{'\n', String.append(u, x)}),
          String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
          r1,
          Equal.trans(String,
            String.append(String.append(String.append(p, n), "]"), SCon{'\n', String.append(u, x)}),
            String.append(String.append(p, n), SCon{']', SCon{'\n', String.append(u, x)}}),
            String.append(p, String.append(n, SCon{']', SCon{'\n', String.append(u, x)}})),
            r2, r3)))))

# ---------------------------------------------------------------------------
# a ledger as tables of rows

# the rows of the `[package]` table
def pkg.rows(n: String, e: String, b: String, h: String) -> List<&2, Row>:
  [Q{"name", n}, Q{"entry", e}, Q{"bin", b}, Q{"hub", h}]

# the rows a source writes
def src.rows(s: M.Source) -> List<&2, Row>:
  match s:
    case M.Hub{named}:
      [Q{"hub", named}]
    case M.Git{url, rev, tag, root, nar, vend}:
      [Q{"git", url}, Q{"rev", rev}, Q{"tag", tag}, Q{"root", root}, Q{"narHash", nar},
        B{"vendor", R.vendor.word(vend)}]

# the rows of a `[deps.<name>]` table
def dep.rows(h: String, e: String, s: M.Source) -> List<&2, Row>:
  Q{"hash", h} <> List.append(&2, Row, src.rows(s), [Q{"entry", e}])

# the rows of a `[tools.<name>]` table
def tool.rows(e: String, b: String, s: M.Source) -> List<&2, Row>:
  List.append(&2, Row, src.rows(s), [Q{"entry", e}, Q{"bin", b}])

def dep.sect(d: M.Dep) -> RSect:
  M.Dep{n, h, e, s} = d
  RSect{"deps." ++ n, dep.rows(h, e, s)}

def tool.sect(pin: M.Tool) -> RSect:
  M.Tool{n, e, b, s} = pin
  RSect{"tools." ++ n, tool.rows(e, b, s)}

def tsects(ts: List<&2, M.Tool>) -> List<&2, RSect>:
  match ts:
    case []:
      []
    case h <> t:
      tool.sect(h) <> tsects(t)

# every dependency's table, ahead of the tables given
def dsects(ds: List<&2, M.Dep>, rest: List<&2, RSect>) -> List<&2, RSect>:
  match ds:
    case []:
      rest
    case h <> t:
      dep.sect(h) <> dsects(t, rest)

# a ledger's tables, in the order the renderer writes them
def lsects(m: M.Manifest) -> List<&2, RSect>:
  M.Manifest{n, e, b, h, ds, ts} = m
  RSect{"package", pkg.rows(n, e, b, h)} <> dsects(ds, tsects(ts))

# the text a ledger's tables after the first write: every table a newline
# first
def rjoin(ss: List<&2, RSect>) -> String:
  String.join.go(rdoc.lines(ss), "", "\n")

# LAW: a table's rows read back when the table does
law rsect_rows:
  for +n: String
  for +rs: List<&2, Row>
  for e: {rsect.ok(RSect{n, rs}) == True{} : Bool}
  {rows.ok(rs) == True{} : Bool}

def rsect_rows(n, rs, e):
  Eq.and.right(Str.clear(n, '\n'), rows.ok(rs),
    Eq.and.right(Bool.not(String.is_empty(n)), Bool.and(Str.clear(n, '\n'), rows.ok(rs)), e))

# LAW: a source's rows are the text the renderer writes for it
law src_text:
  for +s: M.Source
  {rows.text(src.rows(s)) == R.source(s) : String}

def src_text(s):
  match s:
    case M.Hub{+named}:
      Str.append_nil(R.line("hub", named))
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      Equal.cong(String, String,
        y => String.append(R.line("git", url), String.append(R.line("rev", rev),
          String.append(R.line("tag", tag), String.append(R.line("root", root),
            String.append(R.line("narHash", nar), y))))),
        String.append(R.line.bare("vendor", R.vendor.word(vend)), ""),
        R.line.bare("vendor", R.vendor.word(vend)),
        Str.append_nil(R.line.bare("vendor", R.vendor.word(vend))))

# LAW: a table, a blank line first, then the tables after it
law rjoin_cons:
  for +n: String
  for +rs: List<&2, Row>
  for +t: List<&2, RSect>
  {rjoin(RSect{n, rs} <> t)
    == SCon{'\n', String.append(TP.unlines(TP.head.line(n) <> rows.lines(keep(rs))), rjoin(t))}
    : String}

def rjoin_cons(n, rs, t):
  Equal.cong(String, String, y => SCon{'\n', y},
    String.join.go(List.append(&2, String, rows.lines(keep(rs)), "" <> rdoc.lines(t)),
      TP.head.line(n), "\n"),
    String.append(TP.unlines(TP.head.line(n) <> rows.lines(keep(rs))), rjoin(t)),
    TP.join_lines(rows.lines(keep(rs)), TP.head.line(n), rdoc.lines(t)))

# LAW: a dependency as the renderer writes it, ahead of whatever follows, is a
# newline and its table's lines
law dep_text:
  for +n: String
  for +h: String
  for +e: String
  for +s: M.Source
  for +x: String
  for ok: {rows.ok(dep.rows(h, e, s)) == True{} : Bool}
  {String.append(R.dep(M.Dep{n, h, e, s}), x)
    == SCon{'\n', String.append(TP.unlines(TP.head.line("deps." ++ n)
      <> rows.lines(keep(dep.rows(h, e, s)))), x)} : String}

def dep_text(n, h, e, s, x, ok):
  +u = TP.unlines(rows.lines(keep(dep.rows(h, e, s))))
  +lh = R.line("hash", h)
  +le = R.line("entry", e)
  eu = Equal.trans(String, String.append(u, x),
    rows.cat(dep.rows(h, e, s), x),
    String.append(lh, String.append(R.source(s), String.append(le, x))),
    Equal.trans(String, String.append(u, x),
      String.append(rows.text(dep.rows(h, e, s)), x),
      rows.cat(dep.rows(h, e, s), x),
      Equal.cong(String, String, y => String.append(y, x), u, rows.text(dep.rows(h, e, s)),
        rows_text(dep.rows(h, e, s), ok)),
      Equal.sym(String, rows.cat(dep.rows(h, e, s), x),
        String.append(rows.text(dep.rows(h, e, s)), x), rows_cat(dep.rows(h, e, s), x))),
    Equal.cong(String, String, y => String.append(lh, y),
      rows.cat(List.append(&2, Row, src.rows(s), [Q{"entry", e}]), x),
      String.append(R.source(s), String.append(le, x)),
      Equal.trans(String,
        rows.cat(List.append(&2, Row, src.rows(s), [Q{"entry", e}]), x),
        rows.cat(src.rows(s), String.append(le, x)),
        String.append(R.source(s), String.append(le, x)),
        rows_cat_append(src.rows(s), [Q{"entry", e}], x),
        Equal.trans(String,
          rows.cat(src.rows(s), String.append(le, x)),
          String.append(rows.text(src.rows(s)), String.append(le, x)),
          String.append(R.source(s), String.append(le, x)),
          rows_cat(src.rows(s), String.append(le, x)),
          Equal.cong(String, String, y => String.append(y, String.append(le, x)),
            rows.text(src.rows(s)), R.source(s), src_text(s))))))
  ez = Equal.trans(String,
    String.append(String.append(lh, String.append(R.source(s), le)), x),
    String.append(lh, String.append(String.append(R.source(s), le), x)),
    String.append(lh, String.append(R.source(s), String.append(le, x))),
    Eq.append_assoc(lh, String.append(R.source(s), le), x),
    Equal.cong(String, String, y => String.append(lh, y),
      String.append(String.append(R.source(s), le), x),
      String.append(R.source(s), String.append(le, x)),
      Eq.append_assoc(R.source(s), le, x)))
  blk_text("deps.", n, String.append(lh, String.append(R.source(s), le)), u, x,
    Equal.trans(String, String.append(u, x),
      String.append(lh, String.append(R.source(s), String.append(le, x))),
      String.append(String.append(lh, String.append(R.source(s), le)), x),
      eu,
      Equal.sym(String, String.append(String.append(lh, String.append(R.source(s), le)), x),
        String.append(lh, String.append(R.source(s), String.append(le, x))), ez)))

# LAW: and so is a pinned CLI
law tool_text:
  for +n: String
  for +e: String
  for +b: String
  for +s: M.Source
  for +x: String
  for ok: {rows.ok(tool.rows(e, b, s)) == True{} : Bool}
  {String.append(R.tool(M.Tool{n, e, b, s}), x)
    == SCon{'\n', String.append(TP.unlines(TP.head.line("tools." ++ n)
      <> rows.lines(keep(tool.rows(e, b, s)))), x)} : String}

def tool_text(n, e, b, s, x, ok):
  +u = TP.unlines(rows.lines(keep(tool.rows(e, b, s))))
  +le = R.line("entry", e)
  +lb = R.line("bin", b)
  eu = Equal.trans(String, String.append(u, x),
    rows.cat(tool.rows(e, b, s), x),
    String.append(R.source(s), String.append(le, String.append(lb, x))),
    Equal.trans(String, String.append(u, x),
      String.append(rows.text(tool.rows(e, b, s)), x),
      rows.cat(tool.rows(e, b, s), x),
      Equal.cong(String, String, y => String.append(y, x), u, rows.text(tool.rows(e, b, s)),
        rows_text(tool.rows(e, b, s), ok)),
      Equal.sym(String, rows.cat(tool.rows(e, b, s), x),
        String.append(rows.text(tool.rows(e, b, s)), x), rows_cat(tool.rows(e, b, s), x))),
    Equal.trans(String,
      rows.cat(tool.rows(e, b, s), x),
      rows.cat(src.rows(s), String.append(le, String.append(lb, x))),
      String.append(R.source(s), String.append(le, String.append(lb, x))),
      rows_cat_append(src.rows(s), [Q{"entry", e}, Q{"bin", b}], x),
      Equal.trans(String,
        rows.cat(src.rows(s), String.append(le, String.append(lb, x))),
        String.append(rows.text(src.rows(s)), String.append(le, String.append(lb, x))),
        String.append(R.source(s), String.append(le, String.append(lb, x))),
        rows_cat(src.rows(s), String.append(le, String.append(lb, x))),
        Equal.cong(String, String, y => String.append(y, String.append(le, String.append(lb, x))),
          rows.text(src.rows(s)), R.source(s), src_text(s)))))
  ez = Equal.trans(String,
    String.append(String.append(R.source(s), String.append(le, lb)), x),
    String.append(R.source(s), String.append(String.append(le, lb), x)),
    String.append(R.source(s), String.append(le, String.append(lb, x))),
    Eq.append_assoc(R.source(s), String.append(le, lb), x),
    Equal.cong(String, String, y => String.append(R.source(s), y),
      String.append(String.append(le, lb), x),
      String.append(le, String.append(lb, x)),
      Eq.append_assoc(le, lb, x)))
  blk_text("tools.", n, String.append(R.source(s), String.append(le, lb)), u, x,
    Equal.trans(String, String.append(u, x),
      String.append(R.source(s), String.append(le, String.append(lb, x))),
      String.append(String.append(R.source(s), String.append(le, lb)), x),
      eu,
      Equal.sym(String, String.append(String.append(R.source(s), String.append(le, lb)), x),
        String.append(R.source(s), String.append(le, String.append(lb, x))), ez)))

# LAW: the pinned CLIs as the renderer writes them are their tables' lines,
# each table a newline first
law tools_text:
  for +ts: List<&2, M.Tool>
  for +ok: {rsects.ok(tsects(ts)) == True{} : Bool}
  {R.tools(ts) == rjoin(tsects(ts)) : String}

def tools_text(ts, ok):
  match ts:
    case []:
      {==}
    case M.Tool{+n, +e, +b, +s} <> +r:
      +ih = tools_text(r, Eq.and.right(rsect.ok(tool.sect(M.Tool{n, e, b, s})), rsects.ok(tsects(r)), ok))
      Equal.trans(String, R.tools(M.Tool{n, e, b, s} <> r),
        String.append(R.tool(M.Tool{n, e, b, s}), rjoin(tsects(r))),
        rjoin(tsects(M.Tool{n, e, b, s} <> r)),
        Equal.cong(String, String, y => String.append(R.tool(M.Tool{n, e, b, s}), y),
          R.tools(r), rjoin(tsects(r)), ih),
        Equal.trans(String,
          String.append(R.tool(M.Tool{n, e, b, s}), rjoin(tsects(r))),
          SCon{'\n', String.append(TP.unlines(TP.head.line("tools." ++ n)
            <> rows.lines(keep(tool.rows(e, b, s)))), rjoin(tsects(r)))},
          rjoin(tsects(M.Tool{n, e, b, s} <> r)),
          tool_text(n, e, b, s, rjoin(tsects(r)),
            rsect_rows("tools." ++ n, tool.rows(e, b, s),
              Eq.and.left(rsect.ok(tool.sect(M.Tool{n, e, b, s})), rsects.ok(tsects(r)), ok))),
          Equal.sym(String, rjoin(tsects(M.Tool{n, e, b, s} <> r)),
            SCon{'\n', String.append(TP.unlines(TP.head.line("tools." ++ n)
              <> rows.lines(keep(tool.rows(e, b, s)))), rjoin(tsects(r)))},
            rjoin_cons("tools." ++ n, tool.rows(e, b, s), tsects(r)))))

# LAW: and the dependencies, then the pinned CLIs
law deps_text:
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +ok: {rsects.ok(dsects(ds, tsects(ts))) == True{} : Bool}
  {String.append(R.deps(ds), R.tools(ts)) == rjoin(dsects(ds, tsects(ts))) : String}

def deps_text(ds, ts, ok):
  match ds:
    case []:
      tools_text(ts, ok)
    case M.Dep{+n, +h, +e, +s} <> +t:
      +rest = dsects(t, tsects(ts))
      +ih = deps_text(t, ts, Eq.and.right(rsect.ok(dep.sect(M.Dep{n, h, e, s})), rsects.ok(rest), ok))
      Equal.trans(String,
        String.append(String.append(R.dep(M.Dep{n, h, e, s}), R.deps(t)), R.tools(ts)),
        String.append(R.dep(M.Dep{n, h, e, s}), rjoin(rest)),
        rjoin(dsects(M.Dep{n, h, e, s} <> t, tsects(ts))),
        Equal.trans(String,
          String.append(String.append(R.dep(M.Dep{n, h, e, s}), R.deps(t)), R.tools(ts)),
          String.append(R.dep(M.Dep{n, h, e, s}), String.append(R.deps(t), R.tools(ts))),
          String.append(R.dep(M.Dep{n, h, e, s}), rjoin(rest)),
          Eq.append_assoc(R.dep(M.Dep{n, h, e, s}), R.deps(t), R.tools(ts)),
          Equal.cong(String, String, y => String.append(R.dep(M.Dep{n, h, e, s}), y),
            String.append(R.deps(t), R.tools(ts)), rjoin(rest), ih)),
        Equal.trans(String,
          String.append(R.dep(M.Dep{n, h, e, s}), rjoin(rest)),
          SCon{'\n', String.append(TP.unlines(TP.head.line("deps." ++ n)
            <> rows.lines(keep(dep.rows(h, e, s)))), rjoin(rest))},
          rjoin(dsects(M.Dep{n, h, e, s} <> t, tsects(ts))),
          dep_text(n, h, e, s, rjoin(rest),
            rsect_rows("deps." ++ n, dep.rows(h, e, s),
              Eq.and.left(rsect.ok(dep.sect(M.Dep{n, h, e, s})), rsects.ok(rest), ok))),
          Equal.sym(String, rjoin(dsects(M.Dep{n, h, e, s} <> t, tsects(ts))),
            SCon{'\n', String.append(TP.unlines(TP.head.line("deps." ++ n)
              <> rows.lines(keep(dep.rows(h, e, s)))), rjoin(rest))},
            rjoin_cons("deps." ++ n, dep.rows(h, e, s), rest))))

# LAW: a ledger as the renderer writes it is its tables' lines joined by
# newlines
law show_text:
  for +m: M.Manifest
  for +ok: {rsects.ok(lsects(m)) == True{} : Bool}
  {R.show(m) == String.join(rdoc.lines(lsects(m)), "\n") : String}

def show_text(m, ok):
  match m:
    case M.Manifest{+n, +e, +b, +h, +ds, +ts}:
      +d = dsects(ds, tsects(ts))
      +p = pkg.rows(n, e, b, h)
      +pk = {RSect{"package", p} : RSect}
      +dt = deps_text(ds, ts, Eq.and.right(rsect.ok(pk), rsects.ok(d), ok))
      +pt = rows_text(p, rsect_rows("package", p, Eq.and.left(rsect.ok(pk), rsects.ok(d), ok)))
      Equal.trans(String, R.show(M.Manifest{n, e, b, h, ds, ts}),
        "[package]\n" ++ rows.cat(p, rjoin(d)),
        String.join(rdoc.lines(pk <> d), "\n"),
        Equal.cong(String, String,
          y => "[package]\n" ++ String.append(R.line("name", n), String.append(R.line("entry", e),
            String.append(R.line("bin", b), String.append(R.line("hub", h), y)))),
          String.append(R.deps(ds), R.tools(ts)), rjoin(d), dt),
        Equal.trans(String, "[package]\n" ++ rows.cat(p, rjoin(d)),
          "[package]\n" ++ String.append(TP.unlines(rows.lines(keep(p))), rjoin(d)),
          String.join(rdoc.lines(pk <> d), "\n"),
          Equal.cong(String, String, y => "[package]\n" ++ y,
            rows.cat(p, rjoin(d)), String.append(TP.unlines(rows.lines(keep(p))), rjoin(d)),
            Equal.trans(String, rows.cat(p, rjoin(d)), String.append(rows.text(p), rjoin(d)),
              String.append(TP.unlines(rows.lines(keep(p))), rjoin(d)),
              rows_cat(p, rjoin(d)),
              Equal.cong(String, String, y => String.append(y, rjoin(d)),
                rows.text(p), TP.unlines(rows.lines(keep(p))),
                Equal.sym(String, TP.unlines(rows.lines(keep(p))), rows.text(p), pt)))),
          Equal.sym(String, String.join(rdoc.lines(pk <> d), "\n"),
            String.append(TP.unlines("[package]" <> rows.lines(keep(p))), rjoin(d)),
            TP.join_lines(rows.lines(keep(p)), "[package]", rdoc.lines(d)))))

# ---------------------------------------------------------------------------
# a renderable ledger's tables read back

# LAW: the renderer's check for a char is the proofs' one
law clear_same:
  for +s: String
  for +c: Char
  {R.clear(s, c) == Str.clear(s, c) : Bool}

def clear_same(s, c):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      Equal.cong(Bool, Bool, y => Bool.and(Bool.not(Char.is_eq(h, c)), y),
        R.clear(t, c), Str.clear(t, c), clear_same(t, c))

# LAW: a clean value holds no newline
law clean_nl:
  for +s: String
  for +e: {R.clean(s) == True{} : Bool}
  {Str.clear(s, '\n') == True{} : Bool}

def clean_nl(s, e):
  Equal.trans(Bool, Str.clear(s, '\n'), R.clear(s, '\n'), True{},
    Equal.sym(Bool, R.clear(s, '\n'), Str.clear(s, '\n'), clear_same(s, '\n')),
    Eq.and.right(R.clear(s, '\\'), R.clear(s, '\n'),
      Eq.and.right(R.clear(s, '"'), Bool.and(R.clear(s, '\\'), R.clear(s, '\n')), e)))

# LAW: the vendor row reads back whichever bit it carries
law vend_ok:
  for vend: Bool
  {row.ok(B{"vendor", R.vendor.word(vend)}) == True{} : Bool}

def vend_ok(vend):
  match vend:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a clean source's rows, ahead of rows that read back, read back
law src_rows_ok:
  for +s: M.Source
  for +rest: List<&2, Row>
  for es: {R.source.ok(s) == True{} : Bool}
  for er: {rows.ok(rest) == True{} : Bool}
  {rows.ok(List.append(&2, Row, src.rows(s), rest)) == True{} : Bool}

def src_rows_ok(s, rest, es, er):
  match s:
    case M.Hub{+named}:
      Str.and_true(Str.clear(named, '\n'), rows.ok(rest), clean_nl(named, es), er)
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +cs = Eq.and.right(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(R.clean(url), R.clean(rev)),
          Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)))), es)
      +c1 = Eq.and.left(Bool.and(R.clean(url), R.clean(rev)),
        Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar))), cs)
      +c2 = Eq.and.right(Bool.and(R.clean(url), R.clean(rev)),
        Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar))), cs)
      +c3 = Eq.and.right(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)), c2)
      Str.and_true(Str.clear(url, '\n'), rows.ok(List.append(&2, Row,
          [Q{"rev", rev}, Q{"tag", tag}, Q{"root", root}, Q{"narHash", nar},
            B{"vendor", R.vendor.word(vend)}], rest)),
        clean_nl(url, Eq.and.left(R.clean(url), R.clean(rev), c1)),
        Str.and_true(Str.clear(rev, '\n'), rows.ok(List.append(&2, Row,
            [Q{"tag", tag}, Q{"root", root}, Q{"narHash", nar},
              B{"vendor", R.vendor.word(vend)}], rest)),
          clean_nl(rev, Eq.and.right(R.clean(url), R.clean(rev), c1)),
          Str.and_true(Str.clear(tag, '\n'), rows.ok(List.append(&2, Row,
              [Q{"root", root}, Q{"narHash", nar}, B{"vendor", R.vendor.word(vend)}], rest)),
            clean_nl(tag, Eq.and.left(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)), c2)),
            Str.and_true(Str.clear(root, '\n'), rows.ok(List.append(&2, Row,
                [Q{"narHash", nar}, B{"vendor", R.vendor.word(vend)}], rest)),
              clean_nl(root, Eq.and.left(R.clean(root), R.clean(nar), c3)),
              Str.and_true(Str.clear(nar, '\n'), rows.ok(List.append(&2, Row,
                  [B{"vendor", R.vendor.word(vend)}], rest)),
                clean_nl(nar, Eq.and.right(R.clean(root), R.clean(nar), c3)),
                Str.and_true(row.ok(B{"vendor", R.vendor.word(vend)}), rows.ok(rest),
                  vend_ok(vend), er))))))

# LAW: a dependency that can be written has a table that reads back
law dep_sect_ok:
  for +d: M.Dep
  for +e: {R.dep.ok(d) == True{} : Bool}
  {rsect.ok(dep.sect(d)) == True{} : Bool}

def dep_sect_ok(d, e):
  match d:
    case M.Dep{+n, +h, +en, +s}:
      +l = Eq.and.left(Bool.and(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h))),
        Bool.and(R.clean(en), R.source.ok(s)), e)
      +r = Eq.and.right(Bool.and(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h))),
        Bool.and(R.clean(en), R.source.ok(s)), e)
      Str.and_true(Str.clear(n, '\n'), rows.ok(dep.rows(h, en, s)),
        clean_nl(n, Eq.and.left(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h)), l)),
        Str.and_true(Str.clear(h, '\n'),
          rows.ok(List.append(&2, Row, src.rows(s), [Q{"entry", en}])),
          clean_nl(h, Eq.and.right(Bool.not(String.is_empty(h)), R.clean(h),
            Eq.and.right(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h)), l))),
          src_rows_ok(s, [Q{"entry", en}], Eq.and.right(R.clean(en), R.source.ok(s), r),
            Str.and_true(Str.clear(en, '\n'), True{},
              clean_nl(en, Eq.and.left(R.clean(en), R.source.ok(s), r)), {==}))))

# LAW: an empty string is the empty string
law empty_is:
  for +s: String
  for e: {String.is_empty(s) == True{} : Bool}
  {s == "" : String}

def empty_is(s, e):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Eq.bit.absurd(&2, {SCon{c, t} == "" : String}, e)

# LAW: a pinned CLI's source that can be written is a source that can
law tool_src_ok:
  for +s: M.Source
  for e: {R.tool.src.ok(s) == True{} : Bool}
  {R.source.ok(s) == True{} : Bool}

def tool_src_ok(s, e):
  match s:
    case M.Hub{+named}:
      %Equal.sym(String, named, "", empty_is(named, e)) : {R.clean(_) == True{} : Bool}
      {==}
    case M.Git{_url, _rev, _tag, _root, _nar, _vend}:
      e

# LAW: and so does a pinned CLI that can be written
law tool_sect_ok:
  for +pin: M.Tool
  for +e: {R.tool.ok(pin) == True{} : Bool}
  {rsect.ok(tool.sect(pin)) == True{} : Bool}

def tool_sect_ok(pin, e):
  match pin:
    case M.Tool{+n, +en, +b, +s}:
      +r = Eq.and.right(R.clean(n), Bool.and(Bool.and(R.clean(en), R.clean(b)), R.tool.src.ok(s)), e)
      +eb = Eq.and.left(Bool.and(R.clean(en), R.clean(b)), R.tool.src.ok(s), r)
      Str.and_true(Str.clear(n, '\n'), rows.ok(tool.rows(en, b, s)),
        clean_nl(n, Eq.and.left(R.clean(n), Bool.and(Bool.and(R.clean(en), R.clean(b)),
          R.tool.src.ok(s)), e)),
        src_rows_ok(s, [Q{"entry", en}, Q{"bin", b}],
          tool_src_ok(s, Eq.and.right(Bool.and(R.clean(en), R.clean(b)), R.tool.src.ok(s), r)),
          Str.and_true(Str.clear(en, '\n'), rows.ok([Q{"bin", b}]),
            clean_nl(en, Eq.and.left(R.clean(en), R.clean(b), eb)),
            Str.and_true(Str.clear(b, '\n'), True{},
              clean_nl(b, Eq.and.right(R.clean(en), R.clean(b), eb)), {==}))))

# LAW: the tables of pinned CLIs that can be written read back
law tsects_ok:
  for +ts: List<&2, M.Tool>
  for +e: {R.tools.ok(ts) == True{} : Bool}
  {rsects.ok(tsects(ts)) == True{} : Bool}

def tsects_ok(ts, e):
  match ts:
    case []:
      {==}
    case +h <> +t:
      Str.and_true(rsect.ok(tool.sect(h)), rsects.ok(tsects(t)),
        tool_sect_ok(h, Eq.and.left(R.tool.ok(h), R.tools.ok(t), e)),
        tsects_ok(t, Eq.and.right(R.tool.ok(h), R.tools.ok(t), e)))

# LAW: and the dependencies' tables, ahead of tables that read back
law dsects_ok:
  for +ds: List<&2, M.Dep>
  for +rest: List<&2, RSect>
  for +e: {R.deps.ok(ds) == True{} : Bool}
  for er: {rsects.ok(rest) == True{} : Bool}
  {rsects.ok(dsects(ds, rest)) == True{} : Bool}

def dsects_ok(ds, rest, e, er):
  match ds:
    case []:
      er
    case +h <> +t:
      Str.and_true(rsect.ok(dep.sect(h)), rsects.ok(dsects(t, rest)),
        dep_sect_ok(h, Eq.and.left(R.dep.ok(h), R.deps.ok(t), e)),
        dsects_ok(t, rest, Eq.and.right(R.dep.ok(h), R.deps.ok(t), e), er))

# LAW: a renderable ledger's tables read back
law lsects_ok:
  for +m: M.Manifest
  for +e: {R.renderable(m) == True{} : Bool}
  {rsects.ok(lsects(m)) == True{} : Bool}

def lsects_ok(m, e):
  match m:
    case M.Manifest{+n, +en, +b, +h, +ds, +ts}:
      +l = Eq.and.left(Bool.and(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h))),
        Bool.and(R.deps.ok(ds), R.tools.ok(ts)), e)
      +r = Eq.and.right(Bool.and(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h))),
        Bool.and(R.deps.ok(ds), R.tools.ok(ts)), e)
      +l1 = Eq.and.left(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h)), l)
      +l2 = Eq.and.right(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h)), l)
      Str.and_true(rsect.ok(RSect{"package", pkg.rows(n, en, b, h)}),
        rsects.ok(dsects(ds, tsects(ts))),
        Str.and_true(Str.clear(n, '\n'), rows.ok([Q{"entry", en}, Q{"bin", b}, Q{"hub", h}]),
          clean_nl(n, Eq.and.left(R.clean(n), R.clean(en), l1)),
          Str.and_true(Str.clear(en, '\n'), rows.ok([Q{"bin", b}, Q{"hub", h}]),
            clean_nl(en, Eq.and.right(R.clean(n), R.clean(en), l1)),
            Str.and_true(Str.clear(b, '\n'), rows.ok([Q{"hub", h}]),
              clean_nl(b, Eq.and.left(R.clean(b), R.clean(h), l2)),
              Str.and_true(Str.clear(h, '\n'), True{},
                clean_nl(h, Eq.and.right(R.clean(b), R.clean(h), l2)), {==})))),
        dsects_ok(ds, tsects(ts), Eq.and.left(R.deps.ok(ds), R.tools.ok(ts), r),
          tsects_ok(ts, Eq.and.right(R.deps.ok(ds), R.tools.ok(ts), r))))

# LAW: a renderable ledger's text, parsed, is its tables, with no error
law ledger_sections_read:
  for +m: M.Manifest
  for +e: {R.renderable(m) == True{} : Bool}
  {T.parse(R.show(m)) == T.Toml{"", "", [], sects.of(lsects(m))} : T.Toml}

def ledger_sections_read(m, e):
  match m:
    case M.Manifest{+n, +en, +b, +h, +ds, +ts}:
      +ok = lsects_ok(M.Manifest{n, en, b, h, ds, ts}, e)
      %Equal.sym(String, R.show(M.Manifest{n, en, b, h, ds, ts}),
        String.join(rdoc.lines(lsects(M.Manifest{n, en, b, h, ds, ts})), "\n"),
        show_text(M.Manifest{n, en, b, h, ds, ts}, ok))
        : {T.parse(_) == T.Toml{"", "", [], sects.of(lsects(M.Manifest{n, en, b, h, ds, ts}))}
          : T.Toml}
      rsections_read(RSect{"package", pkg.rows(n, en, b, h)}, dsects(ds, tsects(ts)), ok)

# ---------------------------------------------------------------------------
# what the reader finds in a renderable ledger's tables

# whether no row has a key. Proof vocabulary.
def rows.none(rs: List<&2, Row>, +k: String) -> Bool:
  match rs:
    case []:
      True{}
    case r <> t:
      rest = rows.none(t, k)
      Bool.and(Bool.not(String.eq(row.key(r), k)), rest)

# whether at most one row has a key
def rows.once(rs: List<&2, Row>, +k: String) -> Bool:
  match rs:
    case []:
      True{}
    case r <> +t:
      Bool.pick(Bool, String.eq(row.key(r), k), rows.none(t, k), rows.once(t, k))

# LAW: a row's pair answers a lookup with its value when the key is its own
law value_at_row:
  for +r: Row
  for rest: String
  for +k: String
  {T.value.at(row.kv(r), rest, k) == Bool.pick(String, String.eq(row.key(r), k), row.val(r), rest)
    : String}

def value_at_row(r, _rest, _k):
  match r:
    case Q{_k, _v}:
      {==}
    case B{_k, _v}:
      {==}

# LAW: rows none of which has a key answer it with nothing
law none_value:
  for +rs: List<&2, Row>
  for +k: String
  for +e: {rows.none(rs, k) == True{} : Bool}
  {T.value(rows.kvs(rs), k) == "" : String}

def none_value(rs, k, e):
  match rs:
    case []:
      {==}
    case +r <> +t:
      +nk = Eq.not.true(String.eq(row.key(r), k),
        Eq.and.left(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e))
      %Equal.sym(String, T.value.at(row.kv(r), T.value(rows.kvs(t), k), k),
        Bool.pick(String, String.eq(row.key(r), k), row.val(r), T.value(rows.kvs(t), k)),
        value_at_row(r, T.value(rows.kvs(t), k), k))
        : {_ == "" : String}
      %Equal.sym(Bool, String.eq(row.key(r), k), False{}, nk)
        : {Bool.pick(String, _, row.val(r), T.value(rows.kvs(t), k)) == "" : String}
      none_value(t, k, Eq.and.right(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e))

# LAW: one row, kept or dropped, with whether its value is empty given
law none_keep.arm:
  for +r: Row
  for +t: List<&2, Row>
  for +k: String
  for c: Bool
  for ek: {Bool.not(String.eq(row.key(r), k)) == True{} : Bool}
  for ih: {rows.none(keep(t), k) == True{} : Bool}
  {rows.none(keep.put(c, r, keep(t)), k) == True{} : Bool}

def none_keep.arm(r, t, k, c, ek, ih):
  match c:
    case True{}:
      ih
    case False{}:
      Str.and_true(Bool.not(String.eq(row.key(r), k)), rows.none(keep(t), k), ek, ih)

# LAW: and so do the rows kept of them
law none_keep:
  for +rs: List<&2, Row>
  for +k: String
  for +e: {rows.none(rs, k) == True{} : Bool}
  {rows.none(keep(rs), k) == True{} : Bool}

def none_keep(rs, k, e):
  match rs:
    case []:
      {==}
    case +r <> +t:
      none_keep.arm(r, t, k, String.is_empty(row.val(r)),
        Eq.and.left(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e),
        none_keep(t, k, Eq.and.right(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e)))

# LAW: rows none of which has a key have it at most once
law none_once:
  for +rs: List<&2, Row>
  for +k: String
  for +e: {rows.none(rs, k) == True{} : Bool}
  {rows.once(rs, k) == True{} : Bool}

def none_once(rs, k, e):
  match rs:
    case []:
      {==}
    case +r <> +t:
      +nk = Eq.not.true(String.eq(row.key(r), k),
        Eq.and.left(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e))
      %Equal.sym(Bool, String.eq(row.key(r), k), False{}, nk)
        : {Bool.pick(Bool, _, rows.none(t, k), rows.once(t, k)) == True{} : Bool}
      none_once(t, k, Eq.and.right(Bool.not(String.eq(row.key(r), k)), rows.none(t, k), e))

# LAW: the rows after one that has a key at most once have it at most once,
# with whether the first has it given
law once_tail.arm:
  for +t: List<&2, Row>
  for +k: String
  for b: Bool
  for e: {Bool.pick(Bool, b, rows.none(t, k), rows.once(t, k)) == True{} : Bool}
  {rows.once(t, k) == True{} : Bool}

def once_tail.arm(t, k, b, e):
  match b:
    case True{}:
      none_once(t, k, e)
    case False{}:
      e

# LAW: rows that have a key at most once, with the ones that have no value
# dropped, answer it as the rows do
law value_keep.arm:
  for +r: Row
  for +t: List<&2, Row>
  for +k: String
  for c: Bool
  for ec: {String.is_empty(row.val(r)) == c : Bool}
  for b: Bool
  for eb: {String.eq(row.key(r), k) == b : Bool}
  for e: {Bool.pick(Bool, b, rows.none(t, k), rows.once(t, k)) == True{} : Bool}
  for ih: {T.value(rows.kvs(keep(t)), k) == T.value(rows.kvs(t), k) : String}
  {T.value(rows.kvs(keep.put(c, r, keep(t))), k)
    == Bool.pick(String, b, row.val(r), T.value(rows.kvs(t), k)) : String}

def value_keep.arm(r, t, k, c, ec, b, eb, e, ih):
  match c b:
    case True{} True{}:
      Equal.trans(String, T.value(rows.kvs(keep(t)), k), "", row.val(r),
        none_value(keep(t), k, none_keep(t, k, e)),
        Equal.sym(String, row.val(r), "", empty_is(row.val(r), ec)))
    case True{} False{}:
      ih
    case False{} True{}:
      %Equal.sym(String, T.value.at(row.kv(r), T.value(rows.kvs(keep(t)), k), k),
        Bool.pick(String, String.eq(row.key(r), k), row.val(r), T.value(rows.kvs(keep(t)), k)),
        value_at_row(r, T.value(rows.kvs(keep(t)), k), k))
        : {_ == row.val(r) : String}
      %Equal.sym(Bool, String.eq(row.key(r), k), True{}, eb)
        : {Bool.pick(String, _, row.val(r), T.value(rows.kvs(keep(t)), k)) == row.val(r) : String}
      {==}
    case False{} False{}:
      %Equal.sym(String, T.value.at(row.kv(r), T.value(rows.kvs(keep(t)), k), k),
        Bool.pick(String, String.eq(row.key(r), k), row.val(r), T.value(rows.kvs(keep(t)), k)),
        value_at_row(r, T.value(rows.kvs(keep(t)), k), k))
        : {_ == T.value(rows.kvs(t), k) : String}
      %Equal.sym(Bool, String.eq(row.key(r), k), False{}, eb)
        : {Bool.pick(String, _, row.val(r), T.value(rows.kvs(keep(t)), k))
          == T.value(rows.kvs(t), k) : String}
      ih

# LAW: rows that have a key at most once answer it, once the rows with no
# value are dropped, as they did before
law value_keep:
  for +rs: List<&2, Row>
  for +k: String
  for +e: {rows.once(rs, k) == True{} : Bool}
  {T.value(rows.kvs(keep(rs)), k) == T.value(rows.kvs(rs), k) : String}

def value_keep(rs, k, e):
  match rs:
    case []:
      {==}
    case +r <> +t:
      %Equal.sym(String, T.value.at(row.kv(r), T.value(rows.kvs(t), k), k),
        Bool.pick(String, String.eq(row.key(r), k), row.val(r), T.value(rows.kvs(t), k)),
        value_at_row(r, T.value(rows.kvs(t), k), k))
        : {T.value(rows.kvs(keep(r <> t)), k) == _ : String}
      value_keep.arm(r, t, k, String.is_empty(row.val(r)), {==},
        String.eq(row.key(r), k), {==}, e,
        value_keep(t, k, once_tail.arm(t, k, String.eq(row.key(r), k), e)))

# LAW: two tables that answer a source's six keys alike are read as the same
# source
law source_same:
  for +ps: List<&2, T.Kv>
  for +qs: List<&2, T.Kv>
  for e1: {M.value(ps, "git") == M.value(qs, "git") : String}
  for e2: {M.value(ps, "rev") == M.value(qs, "rev") : String}
  for e3: {M.value(ps, "tag") == M.value(qs, "tag") : String}
  for e4: {M.value(ps, "root") == M.value(qs, "root") : String}
  for e5: {M.value(ps, "narHash") == M.value(qs, "narHash") : String}
  for e6: {M.value(ps, "vendor") == M.value(qs, "vendor") : String}
  {M.source_of(ps) == M.source_of(qs) : M.Source}

def source_same(ps, qs, e1, e2, e3, e4, e5, e6):
  %Equal.sym(String, M.value(ps, "git"), M.value(qs, "git"), e1)
    : {M.source.go(String.is_empty(_), _, M.value(ps, "rev"), M.value(ps, "tag"),
        M.root.or(M.value(ps, "root")), M.value(ps, "narHash"), M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "rev"), M.value(qs, "rev"), e2)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), _, M.value(ps, "tag"),
        M.root.or(M.value(ps, "root")), M.value(ps, "narHash"), M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "tag"), M.value(qs, "tag"), e3)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), M.value(qs, "rev"), _,
        M.root.or(M.value(ps, "root")), M.value(ps, "narHash"), M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "root"), M.value(qs, "root"), e4)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), M.value(qs, "rev"),
        M.value(qs, "tag"), M.root.or(_), M.value(ps, "narHash"), M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "narHash"), M.value(qs, "narHash"), e5)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), M.value(qs, "rev"),
        M.value(qs, "tag"), M.root.or(M.value(qs, "root")), _, M.flag(M.value(ps, "vendor")))
      == M.source_of(qs) : M.Source}
  %Equal.sym(String, M.value(ps, "vendor"), M.value(qs, "vendor"), e6)
    : {M.source.go(String.is_empty(M.value(qs, "git")), M.value(qs, "git"), M.value(qs, "rev"),
        M.value(qs, "tag"), M.root.or(M.value(qs, "root")), M.value(qs, "narHash"), M.flag(_))
      == M.source_of(qs) : M.Source}
  {==}

# LAW: rows that have each of a source's keys at most once are read, once
# the rows with no value are dropped, as the same source
law src_keep:
  for +rs: List<&2, Row>
  for s: M.Source
  for o1: {rows.once(rs, "git") == True{} : Bool}
  for o2: {rows.once(rs, "rev") == True{} : Bool}
  for o3: {rows.once(rs, "tag") == True{} : Bool}
  for o4: {rows.once(rs, "root") == True{} : Bool}
  for o5: {rows.once(rs, "narHash") == True{} : Bool}
  for o6: {rows.once(rs, "vendor") == True{} : Bool}
  for es: {M.source_of(rows.kvs(rs)) == s : M.Source}
  {M.source_of(rows.kvs(keep(rs))) == s : M.Source}

def src_keep(rs, s, o1, o2, o3, o4, o5, o6, es):
  Equal.trans(M.Source, M.source_of(rows.kvs(keep(rs))), M.source_of(rows.kvs(rs)), s,
    source_same(rows.kvs(keep(rs)), rows.kvs(rs),
      value_keep(rs, "git", o1), value_keep(rs, "rev", o2), value_keep(rs, "tag", o3),
      value_keep(rs, "root", o4), value_keep(rs, "narHash", o5), value_keep(rs, "vendor", o6)),
    es)

# LAW: the vendor bit rendered reads back as the bit
law flag_word:
  for vend: Bool
  {M.flag(R.vendor.word(vend)) == vend : Bool}

def flag_word(vend):
  match vend:
    case True{}:
      {==}
    case False{}:
      {==}

# LAW: a git source that names its repo and its root is read as itself
law git_source:
  for +url: String
  for rev: String
  for tag: String
  for +root: String
  for nar: String
  for vend: Bool
  for eu: {String.is_empty(url) == False{} : Bool}
  for er: {String.is_empty(root) == False{} : Bool}
  {M.source.go(String.is_empty(url), url, rev, tag, M.root.or(root), nar, M.flag(R.vendor.word(vend)))
    == M.Git{url, rev, tag, root, nar, vend} : M.Source}

def git_source(url, rev, tag, root, nar, vend, eu, er):
  %Equal.sym(Bool, String.is_empty(url), False{}, eu)
    : {M.source.go(_, url, rev, tag, M.root.or(root), nar, M.flag(R.vendor.word(vend)))
      == M.Git{url, rev, tag, root, nar, vend} : M.Source}
  %Equal.sym(Bool, String.is_empty(root), False{}, er)
    : {M.source.go(False{}, url, rev, tag, Bool.pick(String, _, ".", root), nar,
        M.flag(R.vendor.word(vend))) == M.Git{url, rev, tag, root, nar, vend} : M.Source}
  %Equal.sym(Bool, M.flag(R.vendor.word(vend)), vend, flag_word(vend))
    : {M.source.go(False{}, url, rev, tag, root, nar, _)
      == M.Git{url, rev, tag, root, nar, vend} : M.Source}
  {==}

# LAW: a dependency's table, as it reads back, is read as the dependency
law dep_read:
  for +n: String
  for +h: String
  for +en: String
  for +s: M.Source
  for ok: {R.dep.ok(M.Dep{n, h, en, s}) == True{} : Bool}
  {M.dep_of("deps." ++ n, rows.kvs(keep(dep.rows(h, en, s)))) == M.Dep{n, h, en, s} : M.Dep}

def dep_read(n, h, en, s, ok):
  match s:
    case M.Hub{+named}:
      +rs = dep.rows(h, en, M.Hub{named})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", {==}))
        : {M.Dep{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "entry"),
          M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Dep{String.drop(n, 0n), h, _,
          M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hub"), M.value(rows.kvs(rs), "hub"),
        value_keep(rs, "hub", {==}))
        : {M.Dep{String.drop(n, 0n), h, en, M.source.named(_, M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Hub{""},
        src_keep(rs, M.Hub{""}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))
        : {M.Dep{String.drop(n, 0n), h, en, M.source.named(named, _)} == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      %Equal.sym(String, String.drop(n, 0n), n, drop_zero(n))
        : {M.Dep{_, h, en, M.Hub{named}} == M.Dep{n, h, en, M.Hub{named}} : M.Dep}
      {==}
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +rs = dep.rows(h, en, M.Git{url, rev, tag, root, nar, vend})
      +es = Eq.and.right(R.clean(en), R.source.ok(M.Git{url, rev, tag, root, nar, vend}),
        Eq.and.right(Bool.and(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h))),
          Bool.and(R.clean(en), R.source.ok(M.Git{url, rev, tag, root, nar, vend})), ok))
      +ne = Eq.and.left(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(R.clean(url), R.clean(rev)),
          Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)))), es)
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", {==}))
        : {M.Dep{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "entry"),
          M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Dep{String.drop(n, 0n), h, _,
          M.source.named(M.value(rows.kvs(keep(rs)), "hub"), M.source_of(rows.kvs(keep(rs))))}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Git{url, rev, tag, root, nar, vend},
        src_keep(rs, M.Git{url, rev, tag, root, nar, vend}, {==}, {==}, {==}, {==}, {==}, {==},
          git_source(url, rev, tag, root, nar, vend,
            Eq.not.true(String.is_empty(url),
              Eq.and.left(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)),
            Eq.not.true(String.is_empty(root),
              Eq.and.right(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)))))
        : {M.Dep{String.drop(n, 0n), h, en, M.source.named(M.value(rows.kvs(keep(rs)), "hub"), _)}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      %Equal.sym(String, String.drop(n, 0n), n, drop_zero(n))
        : {M.Dep{_, h, en, M.Git{url, rev, tag, root, nar, vend}}
          == M.Dep{n, h, en, M.Git{url, rev, tag, root, nar, vend}} : M.Dep}
      {==}

# LAW: a pinned CLI's table, as it reads back, is read as the pin
law tool_read:
  for +n: String
  for +en: String
  for +b: String
  for +s: M.Source
  for ok: {R.tool.ok(M.Tool{n, en, b, s}) == True{} : Bool}
  {M.tool_of("tools." ++ n, rows.kvs(keep(tool.rows(en, b, s)))) == M.Tool{n, en, b, s} : M.Tool}

def tool_read(n, en, b, s, ok):
  match s:
    case M.Hub{+named}:
      %Equal.sym(String, named, "", empty_is(named,
        Eq.and.right(Bool.and(R.clean(en), R.clean(b)), String.is_empty(named),
          Eq.and.right(R.clean(n), Bool.and(Bool.and(R.clean(en), R.clean(b)),
            String.is_empty(named)), ok))))
        : {M.tool_of("tools." ++ n, rows.kvs(keep(tool.rows(en, b, M.Hub{_}))))
          == M.Tool{n, en, b, M.Hub{_}} : M.Tool}
      +rs = tool.rows(en, b, M.Hub{""})
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Tool{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "bin"), M.source_of(rows.kvs(keep(rs)))}
          == M.Tool{n, en, b, M.Hub{""}} : M.Tool}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "bin"), M.value(rows.kvs(rs), "bin"),
        value_keep(rs, "bin", {==}))
        : {M.Tool{String.drop(n, 0n), en, _, M.source_of(rows.kvs(keep(rs)))} == M.Tool{n, en, b, M.Hub{""}} : M.Tool}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Hub{""},
        src_keep(rs, M.Hub{""}, {==}, {==}, {==}, {==}, {==}, {==}, {==}))
        : {M.Tool{String.drop(n, 0n), en, b, _} == M.Tool{n, en, b, M.Hub{""}} : M.Tool}
      %Equal.sym(String, String.drop(n, 0n), n, drop_zero(n))
        : {M.Tool{_, en, b, M.Hub{""}} == M.Tool{n, en, b, M.Hub{""}} : M.Tool}
      {==}
    case M.Git{+url, +rev, +tag, +root, +nar, +vend}:
      +rs = tool.rows(en, b, M.Git{url, rev, tag, root, nar, vend})
      +es = Eq.and.right(Bool.and(R.clean(en), R.clean(b)),
        R.source.ok(M.Git{url, rev, tag, root, nar, vend}),
        Eq.and.right(R.clean(n), Bool.and(Bool.and(R.clean(en), R.clean(b)),
          R.source.ok(M.Git{url, rev, tag, root, nar, vend})), ok))
      +ne = Eq.and.left(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(R.clean(url), R.clean(rev)),
          Bool.and(R.clean(tag), Bool.and(R.clean(root), R.clean(nar)))), es)
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "entry"), M.value(rows.kvs(rs), "entry"),
        value_keep(rs, "entry", {==}))
        : {M.Tool{String.drop(n, 0n), _, M.value(rows.kvs(keep(rs)), "bin"), M.source_of(rows.kvs(keep(rs)))}
          == M.Tool{n, en, b, M.Git{url, rev, tag, root, nar, vend}} : M.Tool}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "bin"), M.value(rows.kvs(rs), "bin"),
        value_keep(rs, "bin", {==}))
        : {M.Tool{String.drop(n, 0n), en, _, M.source_of(rows.kvs(keep(rs)))}
          == M.Tool{n, en, b, M.Git{url, rev, tag, root, nar, vend}} : M.Tool}
      %Equal.sym(M.Source, M.source_of(rows.kvs(keep(rs))), M.Git{url, rev, tag, root, nar, vend},
        src_keep(rs, M.Git{url, rev, tag, root, nar, vend}, {==}, {==}, {==}, {==}, {==}, {==},
          git_source(url, rev, tag, root, nar, vend,
            Eq.not.true(String.is_empty(url),
              Eq.and.left(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)),
            Eq.not.true(String.is_empty(root),
              Eq.and.right(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root)), ne)))))
        : {M.Tool{String.drop(n, 0n), en, b, _} == M.Tool{n, en, b, M.Git{url, rev, tag, root, nar, vend}} : M.Tool}
      %Equal.sym(String, String.drop(n, 0n), n, drop_zero(n))
        : {M.Tool{_, en, b, M.Git{url, rev, tag, root, nar, vend}}
          == M.Tool{n, en, b, M.Git{url, rev, tag, root, nar, vend}} : M.Tool}
      {==}

# LAW: pinned CLIs' tables hold no dependency
law tdeps_none:
  for +ts: List<&2, M.Tool>
  {M.deps(sects.of(tsects(ts))) == [] : List<&2, M.Dep>}

def tdeps_none(ts):
  match ts:
    case []:
      {==}
    case M.Tool{_n, _e, _b, _s} <> +t:
      tdeps_none(t)

# LAW: the dependencies' tables, ahead of the pinned CLIs', are read as the
# dependencies
law deps_read:
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +e: {R.deps.ok(ds) == True{} : Bool}
  {M.deps(sects.of(dsects(ds, tsects(ts)))) == ds : List<&2, M.Dep>}

def deps_read(ds, ts, e):
  match ds:
    case []:
      tdeps_none(ts)
    case M.Dep{+n, +h, +en, +s} <> +t:
      +ps = rows.kvs(keep(dep.rows(h, en, s)))
      +rest = dsects(t, tsects(ts))
      %Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
        : {M.deps.put(_, T.Sect{"deps." ++ n, ps}, M.deps(sects.of(rest)))
          == M.Dep{n, h, en, s} <> t : List<&2, M.Dep>}
      %Equal.sym(M.Dep, M.dep_of("deps." ++ n, ps), M.Dep{n, h, en, s},
        dep_read(n, h, en, s, Eq.and.left(R.dep.ok(M.Dep{n, h, en, s}), R.deps.ok(t), e)))
        : {_ <> M.deps(sects.of(rest)) == M.Dep{n, h, en, s} <> t : List<&2, M.Dep>}
      %Equal.sym(List<&2, M.Dep>, M.deps(sects.of(rest)), t,
        deps_read(t, ts, Eq.and.right(R.dep.ok(M.Dep{n, h, en, s}), R.deps.ok(t), e)))
        : {M.Dep{n, h, en, s} <> _ == M.Dep{n, h, en, s} <> t : List<&2, M.Dep>}
      {==}

# LAW: the dependencies' tables hold no pinned CLI
law dtools_skip:
  for +ds: List<&2, M.Dep>
  for +rest: List<&2, RSect>
  {M.tools(sects.of(dsects(ds, rest))) == M.tools(sects.of(rest)) : List<&2, M.Tool>}

def dtools_skip(ds, rest):
  match ds:
    case []:
      {==}
    case M.Dep{_n, _h, _e, _s} <> +t:
      dtools_skip(t, rest)

# LAW: the pinned CLIs' tables are read as the pins
law tsects_read:
  for +ts: List<&2, M.Tool>
  for +e: {R.tools.ok(ts) == True{} : Bool}
  {M.tools(sects.of(tsects(ts))) == ts : List<&2, M.Tool>}

def tsects_read(ts, e):
  match ts:
    case []:
      {==}
    case M.Tool{+n, +en, +b, +s} <> +t:
      +ps = rows.kvs(keep(tool.rows(en, b, s)))
      %Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
        : {M.tools.put(_, T.Sect{"tools." ++ n, ps}, M.tools(sects.of(tsects(t))))
          == M.Tool{n, en, b, s} <> t : List<&2, M.Tool>}
      %Equal.sym(M.Tool, M.tool_of("tools." ++ n, ps), M.Tool{n, en, b, s},
        tool_read(n, en, b, s, Eq.and.left(R.tool.ok(M.Tool{n, en, b, s}), R.tools.ok(t), e)))
        : {_ <> M.tools(sects.of(tsects(t))) == M.Tool{n, en, b, s} <> t : List<&2, M.Tool>}
      %Equal.sym(List<&2, M.Tool>, M.tools(sects.of(tsects(t))), t,
        tsects_read(t, Eq.and.right(R.tool.ok(M.Tool{n, en, b, s}), R.tools.ok(t), e)))
        : {M.Tool{n, en, b, s} <> _ == M.Tool{n, en, b, s} <> t : List<&2, M.Tool>}
      {==}

# LAW: pinned CLIs' tables miss no hash
law tmissing:
  for +ts: List<&2, M.Tool>
  {M.missing(sects.of(tsects(ts))) == "" : String}

def tmissing(ts):
  match ts:
    case []:
      {==}
    case M.Tool{_n, _e, _b, _s} <> +t:
      tmissing(t)

# LAW: a dependency's rows name its hash once, whatever its source
law once_hash:
  for +h: String
  for +en: String
  for +s: M.Source
  {rows.once(dep.rows(h, en, s), "hash") == True{} : Bool}

def once_hash(_h, _en, s):
  match s:
    case M.Hub{_named}:
      {==}
    case M.Git{_u, _r, _t, _o, _n, _v}:
      {==}

# LAW: the tables of dependencies that have hashes, ahead of the pins', miss
# no hash
law missing_read:
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +e: {R.deps.ok(ds) == True{} : Bool}
  {M.missing(sects.of(dsects(ds, tsects(ts)))) == "" : String}

def missing_read(ds, ts, e):
  match ds:
    case []:
      tmissing(ts)
    case M.Dep{+n, +h, +en, +s} <> +t:
      +rs = dep.rows(h, en, s)
      +rest = dsects(t, tsects(ts))
      +l = Eq.and.left(Bool.and(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h))),
        Bool.and(R.clean(en), R.source.ok(s)),
        Eq.and.left(R.dep.ok(M.Dep{n, h, en, s}), R.deps.ok(t), e))
      +eh = Eq.not.true(String.is_empty(h),
        Eq.and.left(Bool.not(String.is_empty(h)), R.clean(h),
          Eq.and.right(R.clean(n), Bool.and(Bool.not(String.is_empty(h)), R.clean(h)), l)))
      %Equal.sym(Bool, String.starts_with(n, ""), True{}, Eq.starts_nil(n))
        : {M.missing.at(Bool.and(_, String.is_empty(M.value(rows.kvs(keep(rs)), "hash"))),
          "deps." ++ n, M.missing(sects.of(rest))) == "" : String}
      %Equal.sym(String, M.value(rows.kvs(keep(rs)), "hash"), M.value(rows.kvs(rs), "hash"),
        value_keep(rs, "hash", once_hash(h, en, s)))
        : {M.missing.at(String.is_empty(_), "deps." ++ n, M.missing(sects.of(rest))) == "" : String}
      %Equal.sym(Bool, String.is_empty(h), False{}, eh)
        : {M.missing.at(_, "deps." ++ n, M.missing(sects.of(rest))) == "" : String}
      missing_read(t, ts, Eq.and.right(R.dep.ok(M.Dep{n, h, en, s}), R.deps.ok(t), e))

# LAW: a renderable ledger's tables are read as the ledger
law read_ledger:
  for +n: String
  for +en: String
  for +b: String
  for +h: String
  for +ds: List<&2, M.Dep>
  for +ts: List<&2, M.Tool>
  for +edk: {R.deps.ok(ds) == True{} : Bool}
  for +etk: {R.tools.ok(ts) == True{} : Bool}
  {M.read("", sects.of(lsects(M.Manifest{n, en, b, h, ds, ts})))
    == M.Good{M.Manifest{n, en, b, h, ds, ts}} : M.Read}

def read_ledger(n, en, b, h, ds, ts, edk, etk):
  +p = pkg.rows(n, en, b, h)
  +d = dsects(ds, tsects(ts))
  +s = sects.of(lsects(M.Manifest{n, en, b, h, ds, ts}))
  +g = {M.Good{M.Manifest{n, en, b, h, ds, ts}} : M.Read}
  %Equal.sym(String, M.missing(sects.of(d)), "", missing_read(ds, ts, edk))
    : {M.read.go(String.is_empty(M.problem("", _)), M.problem("", _), s) == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "name"), M.value(rows.kvs(p), "name"),
    value_keep(p, "name", {==}))
    : {M.Good{M.Manifest{_, M.value(rows.kvs(keep(p)), "entry"), M.value(rows.kvs(keep(p)), "bin"),
        M.value(rows.kvs(keep(p)), "hub"), M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "entry"), M.value(rows.kvs(p), "entry"),
    value_keep(p, "entry", {==}))
    : {M.Good{M.Manifest{n, _, M.value(rows.kvs(keep(p)), "bin"),
        M.value(rows.kvs(keep(p)), "hub"), M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "bin"), M.value(rows.kvs(p), "bin"),
    value_keep(p, "bin", {==}))
    : {M.Good{M.Manifest{n, en, _, M.value(rows.kvs(keep(p)), "hub"), M.deps(sects.of(d)),
        M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(String, M.value(rows.kvs(keep(p)), "hub"), M.value(rows.kvs(p), "hub"),
    value_keep(p, "hub", {==}))
    : {M.Good{M.Manifest{n, en, b, _, M.deps(sects.of(d)), M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(List<&2, M.Dep>, M.deps(sects.of(d)), ds, deps_read(ds, ts, edk))
    : {M.Good{M.Manifest{n, en, b, h, _, M.tools(sects.of(d))}} == g : M.Read}
  %Equal.sym(List<&2, M.Tool>, M.tools(sects.of(d)), ts,
    Equal.trans(List<&2, M.Tool>, M.tools(sects.of(d)), M.tools(sects.of(tsects(ts))), ts,
      dtools_skip(ds, tsects(ts)), tsects_read(ts, etk)))
    : {M.Good{M.Manifest{n, en, b, h, ds, _}} == g : M.Read}
  {==}

# The renderable ledger, rendered and read: its tables, then the model.
def Laws.ledger_reads_back(m, e):
  match m:
    case M.Manifest{+n, +en, +b, +h, +ds, +ts}:
      +s = sects.of(lsects(M.Manifest{n, en, b, h, ds, ts}))
      +r = Eq.and.right(Bool.and(Bool.and(R.clean(n), R.clean(en)), Bool.and(R.clean(b), R.clean(h))),
        Bool.and(R.deps.ok(ds), R.tools.ok(ts)), e)
      +edk = Eq.and.left(R.deps.ok(ds), R.tools.ok(ts), r)
      +etk = Eq.and.right(R.deps.ok(ds), R.tools.ok(ts), r)
      Equal.trans(M.Read, M.parse(R.show(M.Manifest{n, en, b, h, ds, ts})),
        M.read("", s), M.Good{M.Manifest{n, en, b, h, ds, ts}},
        Equal.cong(T.Toml, M.Read, t => M.parse.go(t),
          T.parse(R.show(M.Manifest{n, en, b, h, ds, ts})), T.Toml{"", "", [], s},
          ledger_sections_read(M.Manifest{n, en, b, h, ds, ts}, e)),
        read_ledger(n, en, b, h, ds, ts, edk, etk))

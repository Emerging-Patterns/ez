# manifest: the proofs. `bend PROOF.bend` is the gate.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./manifest.bend as M
import ./render.bend as R
import ./ignore.bend as I
import ../check/eq.bend as Eq
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

# LAW: one hash's line names that hash, and a hash that is not there names
# nothing
law hashes_allows.hash:
  for e: Bool
  for +x: String
  for ra: List<&2, String>
  for rv: List<&2, String>
  for ee: {String.is_empty(x) == e : Bool}
  for ih: {I.hashes(ra) == rv : List<&2, String>}
  {I.hashes(I.allows.hash(e, x, ra)) == I.vended.hash(e, x, rv)
    : List<&2, String>}

def hashes_allows.hash(e, x, ra, rv, ee, ih):
  match e:
    case True{}:
      ih
    case False{}:
      Equal.trans(List<&2, String>,
        I.hashes.put(I.kind(I.allow(x)), I.hashes(ra)),
        I.hashes.put(I.Allow{x}, I.hashes(ra)),
        x <> rv,
        Equal.cong(I.Rule, List<&2, String>, r => I.hashes.put(r, I.hashes(ra)),
          I.kind(I.allow(x)), I.Allow{x}, kind_allow(x, ee)),
        Equal.cong(List<&2, String>, List<&2, String>, y => x <> y,
          I.hashes(ra), rv, ih))

# LAW: and a dependency whose tree is not committed has no line
law hashes_allows.put:
  for v: Bool
  for +x: String
  for ra: List<&2, String>
  for rv: List<&2, String>
  for ih: {I.hashes(ra) == rv : List<&2, String>}
  {I.hashes(I.allows.put(v, x, ra)) == I.vended.put(v, x, rv)
    : List<&2, String>}

def hashes_allows.put(v, x, ra, rv, ih):
  match v:
    case True{}:
      hashes_allows.hash(String.is_empty(x), x, ra, rv, {==}, ih)
    case False{}:
      ih

# LAW: the lines ez writes for a ledger name exactly its vendored hashes
law hashes_allows:
  for ds: List<&2, M.Dep>
  {I.hashes(I.allows(ds)) == I.vended(ds) : List<&2, String>}

def hashes_allows(ds):
  match ds:
    case []:
      {==}
    case +d <> +t:
      hashes_allows.put(M.source.vendor(M.source.dep(d)), M.dep.hash(d),
        I.allows(t), I.vended(t), hashes_allows(t))

# LAW: one hash's line is ez's, not the project's
law others_allows.hash:
  for e: Bool
  for +x: String
  for ra: List<&2, String>
  for ee: {String.is_empty(x) == e : Bool}
  for ih: {I.others(ra) == [] : List<&2, String>}
  {I.others(I.allows.hash(e, x, ra)) == [] : List<&2, String>}

def others_allows.hash(e, x, ra, ee, ih):
  match e:
    case True{}:
      ih
    case False{}:
      Equal.trans(List<&2, String>,
        I.others.put(I.kind(I.allow(x)), I.allow(x), I.others(ra)),
        I.others.put(I.Allow{x}, I.allow(x), I.others(ra)),
        [],
        Equal.cong(I.Rule, List<&2, String>,
          r => I.others.put(r, I.allow(x), I.others(ra)),
          I.kind(I.allow(x)), I.Allow{x}, kind_allow(x, ee)),
        ih)

# LAW: and so is a dependency's, when it has one
law others_allows.put:
  for v: Bool
  for +x: String
  for ra: List<&2, String>
  for ih: {I.others(ra) == [] : List<&2, String>}
  {I.others(I.allows.put(v, x, ra)) == [] : List<&2, String>}

def others_allows.put(v, x, ra, ih):
  match v:
    case True{}:
      others_allows.hash(String.is_empty(x), x, ra, {==}, ih)
    case False{}:
      ih

# LAW: none of the lines ez writes for a ledger is the project's
law others_allows:
  for ds: List<&2, M.Dep>
  {I.others(I.allows(ds)) == [] : List<&2, String>}

def others_allows(ds):
  match ds:
    case []:
      {==}
    case +d <> +t:
      others_allows.put(M.source.vendor(M.source.dep(d)), M.dep.hash(d),
        I.allows(t), others_allows(t))

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
      hashes_allows(ds)))

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
      others_allows(ds)))

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

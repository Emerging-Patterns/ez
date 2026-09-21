# manifest: the proofs. `bend PROOF.bend` is the gate.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./manifest.bend as M
import ./render.bend as R
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

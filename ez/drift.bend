# ez/drift: the ledger against the source. A package's `0x<hash>` is written in
# two places, the `[deps.<name>]` section of ez.toml and the `import 0x...` line
# that uses it, so the two can disagree. ez treats the manifest as the record
# and the import lines as the truth, and reports the disagreement rather than
# rewriting anyone's source.
import Base
import ../manifest/manifest.bend as M

# the first of a list of strings, or ""
def head(ps: List<&2, String>) -> String:
  match ps:
    case []:
      ""
    case h <> t:
      h

# the package hash an import line names, or "" when the line names none.
# `import 0x<hash>/<file>.bend as P` is the only shape bend has.
def hash_of(+line: String) -> String:
  Bool.pick(String, String.starts_with(line, "import 0x"),
    head(String.split(String.drop(line, 7n), '/')), "")

# a hash kept, or an unhashed line dropped
def hashes.put(none: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match none:
    case True{}:
      rest
    case False{}:
      h <> rest

# every hash the given lines name
def hashes(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case h <> t:
      +got = hash_of(h)
      hashes.put(String.is_empty(got), got, hashes(t))

# a head dropped when what follows repeats it
def uniq.cut(same: Bool, h: String, r: String, t: List<&2, String>) -> List<&2, String>:
  match same:
    case True{}:
      r <> t
    case False{}:
      h <> (r <> t)

# a head offered to a list that is already deduplicated
def uniq.put(+h: String, rest: List<&2, String>) -> List<&2, String>:
  match rest:
    case []:
      [h]
    case +r <> t:
      uniq.cut(String.eq(h, r), h, r, t)

# a sorted list with its repeats dropped
def uniq(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case []:
      []
    case h <> t:
      uniq.put(h, uniq(t))

# every distinct hash the import lines name, sorted, so a report reads the same
# twice over whatever order the lines arrived in
def imported(ls: List<&2, String>) -> List<&2, String>:
  uniq(List.sort(~String, ~String.is_le, hashes(ls)))

# whether a list holds this string
def has(ss: List<&2, String>, +x: String) -> Bool:
  match ss:
    case []:
      False{}
    case h <> t:
      Bool.or(String.eq(h, x), has(t, x))

# a string kept when the other list lacks it
def missing.put(hit: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rest
    case False{}:
      h <> rest

# the strings of `xs` that `known` does not hold
def missing(xs: List<&2, String>, +known: List<&2, String>) -> List<&2, String>:
  match xs:
    case []:
      []
    case +h <> t:
      missing.put(has(known, h), h, missing(t, known))

# every string with the same words either side of it
def label(ls: List<&2, String>, +pre: String, +post: String) -> List<&2, String>:
  match ls:
    case []:
      []
    case h <> t:
      (pre ++ h ++ post) <> label(t, pre, post)

# a dependency's hash
def dep.hash(d: M.Dep) -> String:
  M.Dep{_n, h, _e, _s} = d
  h

# how a ledger entry nobody imports reads
def dep.line(+d: M.Dep) -> String:
  "drift: " ++ M.dep.name(d) ++ " = " ++ dep.hash(d) ++
  " is in ez.toml but no import line uses it"

# the hashes a ledger's dependencies name
def pinned(ds: List<&2, M.Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case h <> t:
      dep.hash(h) <> pinned(t)

# a dependency reported when nothing imports it
def unused.put(hit: Bool, d: M.Dep, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rest
    case False{}:
      dep.line(d) <> rest

# every dependency of the ledger that no import line uses
def unused(ds: List<&2, M.Dep>, +imports: List<&2, String>) -> List<&2, String>:
  match ds:
    case []:
      []
    case +h <> t:
      unused.put(has(imports, dep.hash(h)), h, unused(t, imports))

# the dependencies of a ledger that was read; one that would not parse has none
def deps_of(r: M.Read) -> List<&2, M.Dep>:
  match r:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, ds} = m
      ds

# both directions of the disagreement: a hash the source imports that the
# ledger never names, and a ledger entry no import line uses
def report.go(+imports: List<&2, String>, +ds: List<&2, M.Dep>) -> List<&2, String>:
  List.append(&2, String,
    label(missing(imports, pinned(ds)), "drift: ",
      " is imported but ez.toml does not name it"),
    unused(ds, imports))

# every disagreement between a repo's import lines and its ledger
def report(ls: List<&2, String>, r: M.Read) -> List<&2, String>:
  report.go(imported(ls), deps_of(r))

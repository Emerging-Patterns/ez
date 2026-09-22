# ez/drift: the ledger against the source. A package's `0x<hash>` is written in
# two places, the `[deps.<name>]` section of ez.toml and the `import 0x...` line
# that uses it, so the two can disagree. ez treats the manifest as the record
# and the import lines as the truth, and reports the disagreement rather than
# rewriting anyone's source.
import Base
import ../manifest/manifest.bend as M
import ./sorted.bend as Sort

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
def hashes.put(none: Bool, hash: String, rest: List<&2, String>) -> List<&2, String>:
  match none:
    case True{}:
      rest
    case False{}:
      hash <> rest

# every hash the given lines name
def hashes(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case []:
      []
    case h <> t:
      +got = hash_of(h)
      hashes.put(String.is_empty(got), got, hashes(t))

# a head dropped when what follows repeats it
def uniq.cut(same: Bool, item: String, next: String, rest: List<&2, String>) -> List<&2, String>:
  match same:
    case True{}:
      next <> rest
    case False{}:
      item <> (next <> rest)

# a head offered to a list that is already deduplicated
def uniq.put(+item: String, rest: List<&2, String>) -> List<&2, String>:
  match rest:
    case []:
      [item]
    case +r <> t:
      uniq.cut(String.eq(item, r), item, r, t)

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
  uniq(Sort.sort(hashes(ls)))

# one step of the scan, with the head's answer in hand. `Bool.or` reduces both
# of its sides, so a scan written with it reads the whole list even when the
# first entry answers. The rest arrives as a thunk.
def has.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether a list holds this string
def has(ss: List<&2, String>, +want: String) -> Bool:
  match ss:
    case []:
      False{}
    case h <> t:
      has.step(String.eq(h, want), _u => has(t, want))

# a string kept when the other list lacks it
def missing.put(hit: Bool, item: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rest
    case False{}:
      item <> rest

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
def dep.hash(dependency: M.Dep) -> String:
  M.Dep{_n, h, _e, _s} = dependency
  h

# how a ledger entry nobody imports reads
def dep.line(+dependency: M.Dep) -> String:
  "drift: " ++ M.dep.name(dependency) ++ " = " ++ dep.hash(dependency) ++
  " is in ez.toml but no import line uses it"

# the hashes a ledger's dependencies name
def pinned(ds: List<&2, M.Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case h <> t:
      dep.hash(h) <> pinned(t)

# a dependency reported when nothing imports it
def unused.put(hit: Bool, dependency: M.Dep, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rest
    case False{}:
      dep.line(dependency) <> rest

# every dependency of the ledger that no import line uses
def unused(ds: List<&2, M.Dep>, +imports: List<&2, String>) -> List<&2, String>:
  match ds:
    case []:
      []
    case +h <> t:
      unused.put(has(imports, dep.hash(h)), h, unused(t, imports))

# the dependencies of a ledger that was read; one that would not parse has none
def deps_of(ledger: M.Read) -> List<&2, M.Dep>:
  match ledger:
    case M.Bad{_why}:
      []
    case M.Good{m}:
      M.Manifest{_n, _e, _b, ds, _ts} = m
      ds

# both directions of the disagreement: a hash the source imports that the
# ledger never names, and a ledger entry no import line uses
def report.go(+imports: List<&2, String>, +ds: List<&2, M.Dep>) -> List<&2, String>:
  List.append(&2, String,
    label(missing(imports, pinned(ds)), "drift: ",
      " is imported but ez.toml does not name it"),
    unused(ds, imports))

# every disagreement between a repo's import lines and its ledger
def report(ls: List<&2, String>, ledger: M.Read) -> List<&2, String>:
  report.go(imported(ls), deps_of(ledger))

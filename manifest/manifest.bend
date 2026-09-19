# manifest/manifest: the dependency ledger. Bend's import lines carry a bare
# `0x<hash>`, which says nothing about what the package is or where it came
# from, and nothing in a repo lists them. ez.toml is that list: every package
# the repo imports, by name, with its hash and its origin.
import Base
import ./toml.bend as T

# where a package's bytes come from. A hub package needs nothing else; a git one
# pins a commit, and remembers the tag that was asked for so an upgrade knows
# what to re-resolve.
type Source is Data:
  Hub{}
  Git{url: String, rev: String, tag: String}

# one tracked dependency
type Dep is Data:
  Dep{name: String, hash: String, entry: String, source: Source}

# the ledger: this package, and everything it depends on
type Manifest is Data:
  Manifest{name: String, entry: String, deps: List<&2, Dep>}

# a manifest, or why it could not be read
type Read is Data:
  Bad{why: String}
  Good{m: Manifest}

# this pair's value when the key matches, otherwise whatever the rest of the
# section gave
def value.at(kv: T.Kv, rest: String, key: String) -> String:
  T.Kv{k, v} = kv
  Bool.pick(String, String.eq(k, key), v, rest)

# the value written for a key in a section, or "" when it is absent. The scan
# recurses first and picks after, so no recursive call hides inside a branch.
def value(pairs: List<&2, T.Kv>, +key: String) -> String:
  match pairs:
    case []:
      ""
    case h <> t:
      value.at(h, value(t, key), key)

# this section's pairs when its name matches, otherwise the rest's
def pairs.at(s: T.Sect, rest: List<&2, T.Kv>, name: String) -> List<&2, T.Kv>:
  T.Sect{n, ps} = s
  Bool.pick(List<&2, T.Kv>, String.eq(n, name), ps, rest)

# the pairs of the section with this name, or none
def pairs_of(ss: List<&2, T.Sect>, +name: String) -> List<&2, T.Kv>:
  match ss:
    case []:
      []
    case h <> t:
      pairs.at(h, pairs_of(t, name), name)

# no `git` key means the package lives on the hub
def source.go(hub: Bool, url: String, rev: String, tag: String) -> Source:
  match hub:
    case True{}:
      Hub{}
    case False{}:
      Git{url, rev, tag}

# where a dependency's section says its bytes come from
def source_of(+pairs: List<&2, T.Kv>) -> Source:
  source.go(String.is_empty(value(pairs, "git")), value(pairs, "git"),
    value(pairs, "rev"), value(pairs, "tag"))

# a `[deps.<name>]` section as a dependency
def dep_of(+full: String, +pairs: List<&2, T.Kv>) -> Dep:
  Dep{String.drop(full, 5n), value(pairs, "hash"), value(pairs, "entry"), source_of(pairs)}

# a section joins the dependencies only when it is a `[deps.<name>]`
def deps.put(is_dep: Bool, s: T.Sect, rest: List<&2, Dep>) -> List<&2, Dep>:
  match is_dep:
    case True{}:
      T.Sect{n, ps} = s
      dep_of(n, ps) <> rest
    case False{}:
      rest

# a section's name, for deciding what it is
def name_of(s: T.Sect) -> String:
  T.Sect{n, _ps} = s
  n

# every `[deps.<name>]` section, as dependencies, in the order written
def deps(ss: List<&2, T.Sect>) -> List<&2, Dep>:
  match ss:
    case +h <> t:
      deps.put(String.starts_with(name_of(h), "deps."), h, deps(t))
    case []:
      []

# a dependency with no hash cannot be resolved, so it is reported by name
def missing.at(bad: Bool, name: String, rest: String) -> String:
  match bad:
    case True{}:
      name
    case False{}:
      rest

# a `[deps.<name>]` section is missing its hash when the key is absent
def missing.is(s: T.Sect) -> Bool:
  T.Sect{n, ps} = s
  Bool.and(String.starts_with(n, "deps."), String.is_empty(value(ps, "hash")))

# the first dependency section with no hash, or "" when every one has one
def missing(ss: List<&2, T.Sect>) -> String:
  match ss:
    case +h <> t:
      missing.at(missing.is(h), name_of(h), missing(t))
    case []:
      ""

# the first problem with the document, or "" when there is none. A syntax error
# comes first, since a section that did not parse cannot be judged.
def problem(+bad: String, +miss: String) -> String:
  Bool.pick(String, String.is_empty(bad),
    Bool.pick(String, String.is_empty(miss), "", miss ++ " has no hash"),
    bad)

# the ledger, once the document is known to be sound
def build(+ss: List<&2, T.Sect>) -> Read:
  Good{Manifest{value(pairs_of(ss, "package"), "name"),
    value(pairs_of(ss, "package"), "entry"), deps(ss)}}

# the ledger, or the problem that stopped it
def read.go(ok: Bool, why: String, ss: List<&2, T.Sect>) -> Read:
  match ok:
    case True{}:
      build(ss)
    case False{}:
      Bad{why}

# the sections judged, then read
def read(+bad: String, +ss: List<&2, T.Sect>) -> Read:
  read.go(String.is_empty(problem(bad, missing(ss))),
    problem(bad, missing(ss)), ss)

# the parsed document, taken apart
def parse.go(t: T.Toml) -> Read:
  T.Toml{bad, _name, _pairs, sects} = t
  read(bad, sects)

# the ledger written in an ez.toml
def parse(text: String) -> Read:
  parse.go(T.parse(text))

# how a dependency reads on one line
def show.source(s: Source) -> String:
  match s:
    case Hub{}:
      "hub"
    case Git{_url, _rev, _tag}:
      "git"

# `<name>=<hash>@<hub|git>`
def show.dep(d: Dep) -> String:
  Dep{n, h, _entry, src} = d
  n ++ "=" ++ h ++ "@" ++ show.source(src)

# every dependency shown, in the order written. Base's List.map is over a
# one-use list, and these are two-use, so the walk is written out.
def show.deps(ds: List<&2, Dep>) -> List<&2, String>:
  match ds:
    case []:
      []
    case h <> t:
      show.dep(h) <> show.deps(t)

# the ledger on one line, for a test or a report
def show.m(m: Manifest) -> String:
  Manifest{n, e, ds} = m
  n ++ " " ++ e ++ " " ++ String.join(show.deps(ds), " ")

# the ledger, or the error, on one line
def show(r: Read) -> String:
  match r:
    case Bad{why}:
      "error: " ++ why
    case Good{m}:
      show.m(m)

# this dependency when its name matches, otherwise whatever the rest gave
def find.pick(hit: Bool, d: Dep, rest: Dep) -> Dep:
  match hit:
    case True{}:
      d
    case False{}:
      rest

# the dependency of this name, or a blank one
def find.at(+d: Dep, rest: Dep, name: String) -> Dep:
  Dep{n, _h, _e, _s} = d
  find.pick(String.eq(n, name), d, rest)

# the dependency of this name, or one with empty fields
def find(ds: List<&2, Dep>, +name: String) -> Dep:
  match ds:
    case []:
      Dep{"", "", "", Hub{}}
    case h <> t:
      find.at(h, find(t, name), name)

# the named dependency of a ledger that was read
def dep(r: Read, name: String) -> Dep:
  match r:
    case Bad{_why}:
      Dep{"", "", "", Hub{}}
    case Good{m}:
      Manifest{_n, _e, ds} = m
      find(ds, name)

# the commit a dependency is pinned to, or "" when it is a hub package
def source.rev(s: Source) -> String:
  match s:
    case Hub{}:
      ""
    case Git{_url, rev, _tag}:
      rev

# the tag a dependency was asked for, or "" when it was pinned by commit
def source.tag(s: Source) -> String:
  match s:
    case Hub{}:
      ""
    case Git{_url, _rev, tag}:
      tag

# the source of a dependency that was found
def source.dep(d: Dep) -> Source:
  Dep{_n, _h, _e, s} = d
  s

# the commit the named dependency is pinned to
def rev_of(r: Read, name: String) -> String:
  source.rev(source.dep(dep(r, name)))

# the tag the named dependency was asked for
def tag_of(r: Read, name: String) -> String:
  source.tag(source.dep(dep(r, name)))

# manifest/manifest: the dependency ledger. Bend's import lines carry a bare
# `0x<hash>`, which says nothing about what the package is or where it came
# from, and nothing in a repo lists them. ez.toml is that list: every package
# the repo imports, by name, with its hash and its origin.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T

# where a package's bytes come from. A hub package needs nothing else, though
# one added by its `<name>@<version>` keeps it, which is what its import lines
# say and what the hub named the hash by; a git one pins a commit, and
# remembers the tag that was asked for so an upgrade knows what to
# re-resolve. It also carries the two facts nothing can work out again
# without the checkout: the directory inside it the package's paths are written
# from, and the NAR hash nix rebuilds it by. They live here, in the file that is
# committed, because a clone gets the ledger and not the vendoring cache.
# `vend` is the committed tree: the package is allowlisted under `.ez/lib` and
# an upgrade that moves it lays the new hash there. Absent, it is not.
type Source is Data:
  Hub{named: String}
  Git{url: String, rev: String, tag: String, root: String, nar: String, vend: Bool}

# one tracked dependency
type Dep is Data:
  Dep{name: String, hash: String, entry: String, source: Source}

# one pinned CLI. The git fields are a dependency's. It is not a package:
# it has no `0x` name, it is not imported, and it is not put on BEND_LIB.
# `entry` and `bin` name the file to build when the tool's own ledger should
# not be the one.
type Tool is Data:
  Tool{name: String, entry: String, bin: String, source: Source}

# the ledger: this package, the file `ez build` and `ez run` take, the file
# `ez tool run`, `install` and `upgrade` build when one is named, the hub its
# packages come from ("" for bend's own), everything the package depends on,
# and every CLI it pins
type Manifest is Data:
  Manifest{name: String, entry: String, bin: String, hub: String,
    deps: List<&2, Dep>, tools: List<&2, Tool>}

# a manifest, or why it could not be read
type Read is Data:
  Bad{why: String}
  Good{m: Manifest}

# the value written for a key in a section, or "" when it is absent
def value(pairs: List<&2, T.Kv>, key: String) -> String:
  T.value(pairs, key)

# this section's pairs when its name matches, otherwise the rest's
def pairs.at(sect: T.Sect, rest: List<&2, T.Kv>, name: String) -> List<&2, T.Kv>:
  T.Sect{n, ps} = sect
  Bool.pick(List<&2, T.Kv>, String.eq(n, name), ps, rest)

# the pairs of the section with this name, or none
def pairs_of(ss: List<&2, T.Sect>, +name: String) -> List<&2, T.Kv>:
  match ss:
    case []:
      []
    case h <> t:
      pairs.at(h, pairs_of(t, name), name)

# `vendor = true`, bare or quoted, is the only spelling that commits the tree
def flag(+word: String) -> Bool:
  String.eq(word, "true")

# no `git` key means the package lives on the hub
def source.go(hub: Bool, url: String, rev: String, tag: String, root: String, nar: String, vend: Bool) -> Source:
  match hub:
    case True{}:
      Hub{""}
    case False{}:
      Git{url, rev, tag, root, nar, vend}

# a hub source, with the `<name>@<version>` a dependency's section records
# under `hub`, "" for none. A git source keeps no name, and neither does a
# tool: a tool is not imported, so nothing names it.
def source.named(named: String, src: Source) -> Source:
  match src:
    case Hub{_old}:
      Hub{named}
    case Git{url, rev, tag, root, nar, vend}:
      Git{url, rev, tag, root, nar, vend}

# a git section that names no root was written from the top of its checkout,
# which is the root a lock already spells out as "." and the only one a ledger
# written before this key existed can have meant
def root.or(+dir: String) -> String:
  Bool.pick(String, String.is_empty(dir), ".", dir)

# where a dependency's section says its bytes come from
def source_of(+pairs: List<&2, T.Kv>) -> Source:
  source.go(String.is_empty(value(pairs, "git")), value(pairs, "git"),
    value(pairs, "rev"), value(pairs, "tag"), root.or(value(pairs, "root")),
    value(pairs, "narHash"), flag(value(pairs, "vendor")))

# a `[deps.<name>]` section as a dependency. A hub dependency added by its
# `<name>@<version>` records it as `hub`, beside the hash it named when it
# was added, as a git dependency records its tag beside its rev.
def dep_of(+full: String, +pairs: List<&2, T.Kv>) -> Dep:
  Dep{String.drop(full, 5n), value(pairs, "hash"), value(pairs, "entry"),
    source.named(value(pairs, "hub"), source_of(pairs))}

# a dependency's own name, for finding or replacing it
def dep.name(dependency: Dep) -> String:
  Dep{n, _h, _e, _s} = dependency
  n

# a dependency's hash, which is the `0x` name its import line carries
def dep.hash(dependency: Dep) -> String:
  Dep{_n, h, _e, _s} = dependency
  h

# the file inside the package a dependency was added by, which is the file its
# hash was computed from
def dep.entry(dependency: Dep) -> String:
  Dep{_n, _h, e, _s} = dependency
  e

# a section joins the dependencies only when it is a `[deps.<name>]`
def deps.put(is_dep: Bool, sect: T.Sect, rest: List<&2, Dep>) -> List<&2, Dep>:
  match is_dep:
    case True{}:
      T.Sect{n, ps} = sect
      dep_of(n, ps) <> rest
    case False{}:
      rest

# a section's name, for deciding what it is
def name_of(sect: T.Sect) -> String:
  T.Sect{n, _ps} = sect
  n

# every `[deps.<name>]` section, as dependencies, in the order written
def deps(ss: List<&2, T.Sect>) -> List<&2, Dep>:
  match ss:
    case +h <> t:
      deps.put(String.starts_with(name_of(h), "deps."), h, deps(t))
    case []:
      []

# a `[tools.<name>]` section as a pinned CLI. The prefix is `tools.`
def tool_of(+full: String, +pairs: List<&2, T.Kv>) -> Tool:
  Tool{String.drop(full, 6n), value(pairs, "entry"), value(pairs, "bin"),
    source_of(pairs)}

# a tool's own name
def tool.name(pin: Tool) -> String:
  Tool{n, _e, _b, _s} = pin
  n

# the file a pin names as its entry, or "" when the tool's ledger names it
def tool.entry(pin: Tool) -> String:
  Tool{_n, e, _b, _s} = pin
  e

# the file a pin names as its binary, or "" when the tool's ledger names it
def tool.bin(pin: Tool) -> String:
  Tool{_n, _e, b, _s} = pin
  b

# where a pinned CLI's bytes come from
def tool.source(pin: Tool) -> Source:
  Tool{_n, _e, _b, s} = pin
  s

# a section joins the tools only when it is a `[tools.<name>]`
def tools.put(is_tool: Bool, sect: T.Sect, rest: List<&2, Tool>) -> List<&2, Tool>:
  match is_tool:
    case True{}:
      T.Sect{n, ps} = sect
      tool_of(n, ps) <> rest
    case False{}:
      rest

# every `[tools.<name>]` section, as pinned CLIs, in the order written
def tools(ss: List<&2, T.Sect>) -> List<&2, Tool>:
  match ss:
    case +h <> t:
      tools.put(String.starts_with(name_of(h), "tools."), h, tools(t))
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
def missing.is(sect: T.Sect) -> Bool:
  T.Sect{n, ps} = sect
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
    value(pairs_of(ss, "package"), "entry"),
    value(pairs_of(ss, "package"), "bin"),
    value(pairs_of(ss, "package"), "hub"), deps(ss), tools(ss)}}

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
def parse.go(toml: T.Toml) -> Read:
  T.Toml{bad, _name, _pairs, sects} = toml
  read(bad, sects)

# the ledger written in an ez.toml
def parse(text: String) -> Read:
  parse.go(T.parse(text))

# how a dependency reads on one line
def show.source(src: Source) -> String:
  match src:
    case Hub{_named}:
      "hub"
    case Git{_url, _rev, _tag, _root, _nar, _vend}:
      "git"

# `<name>=<hash>@<hub|git>`
def show.dep(dependency: Dep) -> String:
  Dep{n, h, _entry, src} = dependency
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
def show.m(manifest: Manifest) -> String:
  Manifest{n, e, _b, _h, ds, _ts} = manifest
  n ++ " " ++ e ++ " " ++ String.join(show.deps(ds), " ")

# the ledger, or the error, on one line
def show(ledger: Read) -> String:
  match ledger:
    case Bad{why}:
      "error: " ++ why
    case Good{m}:
      show.m(m)

# this dependency when its name matches, otherwise whatever the rest gave
def find.pick(hit: Bool, dependency: Dep, rest: Dep) -> Dep:
  match hit:
    case True{}:
      dependency
    case False{}:
      rest

# the dependency of this name, or a blank one
def find.at(+dependency: Dep, rest: Dep, name: String) -> Dep:
  Dep{n, _h, _e, _s} = dependency
  find.pick(String.eq(n, name), dependency, rest)

# the dependency of this name, or one with empty fields
def find(ds: List<&2, Dep>, +name: String) -> Dep:
  match ds:
    case []:
      Dep{"", "", "", Hub{""}}
    case h <> t:
      find.at(h, find(t, name), name)

# the named dependency of a ledger that was read
def dep(ledger: Read, name: String) -> Dep:
  match ledger:
    case Bad{_why}:
      Dep{"", "", "", Hub{""}}
    case Good{m}:
      Manifest{_n, _e, _b, _h, ds, _ts} = m
      find(ds, name)

# the commit a dependency is pinned to, or "" when it is a hub package
def source.rev(src: Source) -> String:
  match src:
    case Hub{_named}:
      ""
    case Git{_url, rev, _tag, _root, _nar, _vend}:
      rev

# the tag a dependency was asked for, or "" when it was pinned by commit
def source.tag(src: Source) -> String:
  match src:
    case Hub{_named}:
      ""
    case Git{_url, _rev, tag, _root, _nar, _vend}:
      tag

# the repo a dependency was vendored from, or "" when it is a hub package
def source.url(src: Source) -> String:
  match src:
    case Hub{_named}:
      ""
    case Git{url, _rev, _tag, _root, _nar, _vend}:
      url

# the directory inside the checkout a dependency's paths are written from
def source.root(src: Source) -> String:
  match src:
    case Hub{_named}:
      ""
    case Git{_url, _rev, _tag, root, _nar, _vend}:
      root

# the NAR hash nix rebuilds a dependency's checkout by
def source.nar(src: Source) -> String:
  match src:
    case Hub{_named}:
      ""
    case Git{_url, _rev, _tag, _root, nar, _vend}:
      nar

# the `<name>@<version>` a hub dependency was added by, or "" for one added
# by its hash, and for a git one
def source.nv(src: Source) -> String:
  match src:
    case Hub{named}:
      named
    case Git{_url, _rev, _tag, _root, _nar, _vend}:
      ""

# whether a dependency names a repo rather than the hub
def source.is_git(src: Source) -> Bool:
  match src:
    case Hub{_named}:
      False{}
    case Git{_url, _rev, _tag, _root, _nar, _vend}:
      True{}

# whether an upgrade that moves this dependency also commits the new tree
def source.vendor(src: Source) -> Bool:
  match src:
    case Hub{_named}:
      False{}
    case Git{_url, _rev, _tag, _root, _nar, vend}:
      vend

# the source of a dependency that was found
def source.dep(dependency: Dep) -> Source:
  Dep{_n, _h, _e, s} = dependency
  s

# the commit the named dependency is pinned to
def rev_of(ledger: Read, name: String) -> String:
  source.rev(source.dep(dep(ledger, name)))

# the tag the named dependency was asked for
def tag_of(ledger: Read, name: String) -> String:
  source.tag(source.dep(dep(ledger, name)))

# the hub a ledger's packages come from: the `hub` its `[package]` table
# names, or bend's own when it names none. It is read from the committed
# ledger and not from the environment, so two checkouts of one commit lock
# against the same hub whatever their shells say.
def hub.or(+url: String) -> String:
  Bool.pick(String, String.is_empty(url), "https://hub.bend-lang.com", url)

# the hub of a ledger that was read. One that would not parse names none, and
# so names bend's.
def hub_of(ledger: Read) -> String:
  match ledger:
    case Bad{_why}:
      hub.or("")
    case Good{m}:
      Manifest{_n, _e, _b, h, _ds, _ts} = m
      hub.or(h)

# the pinned CLIs of a ledger that was read; one that would not parse has none
def tools_of(ledger: Read) -> List<&2, Tool>:
  match ledger:
    case Bad{_why}:
      []
    case Good{m}:
      Manifest{_n, _e, _b, _h, _ds, ts} = m
      ts

# this tool when its name matches, otherwise whatever the rest gave
def tool.find.pick(hit: Bool, pin: Tool, rest: Tool) -> Tool:
  match hit:
    case True{}:
      pin
    case False{}:
      rest

# the tool of this name, or a blank one
def tool.find.at(+pin: Tool, rest: Tool, +name: String) -> Tool:
  tool.find.pick(String.eq(tool.name(pin), name), pin, rest)

# the tool of this name, or one with empty fields
def tool.find(ts: List<&2, Tool>, +name: String) -> Tool:
  match ts:
    case []:
      Tool{"", "", "", Hub{""}}
    case h <> t:
      tool.find.at(h, tool.find(t, name), name)

# the rest of the scan only when this one was not it
def tool.step(hit: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether the ledger pins a CLI of this name
def tool.has(ts: List<&2, Tool>, +name: String) -> Bool:
  match ts:
    case []:
      False{}
    case +h <> t:
      tool.step(String.eq(tool.name(h), name), _u => tool.has(t, name))

# an empty `--package` is every tool; a name is that one
def tool.known.go(all: Bool, ts: List<&2, Tool>, +name: String) -> Bool:
  match all:
    case True{}:
      True{}
    case False{}:
      tool.has(ts, name)

# whether `--package` names a pinned CLI, or names nothing and so names all
def tool.known(+only: String, ts: List<&2, Tool>) -> Bool:
  tool.known.go(String.is_empty(only), ts, only)

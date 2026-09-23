# ez/named: the name `ez add` records a dependency under, in the order cargo
# names one. A source the ledger already holds keeps the name the ledger gave
# it. Otherwise a package that is an ez project is named by its own
# `[package] name`, when that is a TOML bare key; otherwise a repository by its
# own name, and a directory by the directory's. The entry file names nothing,
# because most packages call theirs `main.bend`, and two of them would share
# one `[deps.main]`. A name the ledger gives to another source is refused
# rather than written over.
import Base
import ../manifest/manifest.bend as M
import ./target.bend as Tgt

# a text walked from its end: whether a slash has been passed yet, and what
# lies after the last one
type Seen is Data:
  Seen{slash: Bool, last: String}

# one char in front of what was seen, when no slash has been passed yet
def last.at(slash: Bool, ch: Char, rest: String) -> Seen:
  match slash:
    case True{}:
      Seen{True{}, rest}
    case False{}:
      Seen{False{}, SCon{ch, rest}}

# one char in front of what was seen. Once a slash has been passed, nothing
# further left changes the answer.
def last.step(+ch: Char, seen: Seen) -> Seen:
  Seen{slash, rest} = seen
  match slash:
    case True{}:
      Seen{True{}, rest}
    case False{}:
      last.at(Char.is_eq(ch, '/'), ch, rest)

# the text after its last slash, and whether it had one
def last(text: String) -> Seen:
  match text:
    case SNil{}:
      Seen{False{}, ""}
    case SCon{+h, t}:
      last.step(h, last(t))

# what lies after the last slash
def leaf.of(seen: Seen) -> String:
  Seen{_slash, rest} = seen
  rest

# the last component of a path, a slug or a url
def leaf(text: String) -> String:
  leaf.of(last(text))

# the name a source gives itself. A remote is its slug's last component, which
# is the repository with any `.git` already off; a path is the last component
# of the directory it was resolved to.
def called(place: Tgt.Place, +url: String) -> String:
  match place:
    case Tgt.Bad{_why}:
      ""
    case Tgt.Local{_path}:
      leaf(url)
    case Tgt.Remote{_url, slug}:
      leaf(slug)

# one char of a key, with the rest still to be asked about. The rest arrives
# as a thunk, so a char that ends the key ends the walk.
def bare.step(ok: Bool, rest: Unit -> Bool) -> Bool:
  match ok:
    case True{}:
      rest(Unit{})
    case False{}:
      False{}

# the rest of a TOML bare key: letters, digits, `-` and `_`
def bare.rest(text: String) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{+h, t}:
      bare.step(Tgt.plain.at(h), _u => bare.rest(t))

# a TOML bare key: at least one char, each a letter, a digit, `-` or `_`. Only
# such a name can stand in `[deps.<name>]` unquoted.
def bare(text: String) -> Bool:
  match text:
    case SNil{}:
      False{}
    case SCon{+h, t}:
      bare.step(Tgt.plain.at(h), _u => bare.rest(t))

# whether a source is this git url
def from(src: M.Source, +url: String) -> Bool:
  match src:
    case M.Hub{}:
      False{}
    case M.Git{u, _rev, _tag, _root, _nar, _vend}:
      String.eq(u, url)

# a dependency's name when it is this source, or the answer further on
def had.at(same: Bool, name: String, rest: String) -> String:
  match same:
    case True{}:
      name
    case False{}:
      rest

# the name the ledger already gives this url, first in document order, or the
# fresh one when it gives none. A re-add is then the same entry, whatever the
# ledger called it.
def had(ds: List<&2, M.Dep>, +url: String, fresh: String) -> String:
  match ds:
    case []:
      fresh
    case h <> t:
      M.Dep{n, _h, _e, s} = h
      had.at(from(s, url), n, had(t, url, fresh))

# the package's own name when it is a bare key, or the name its source gives
# it. A name that could not stand as a key falls through, not refused.
def own(+pkg: String, +fresh: String) -> String:
  Bool.pick(String, bare(pkg), pkg, fresh)

# the name a dependency is recorded under: the ledger's for this source, else
# the package's own, else its source's
def name(ds: List<&2, M.Dep>, +url: String, +pkg: String, +fresh: String) -> String:
  had(ds, url, own(pkg, fresh))

# the first dependency of this name, asked whether it is another source
def clash.at(hit: Bool, src: M.Source, +url: String, rest: Bool) -> Bool:
  match hit:
    case True{}:
      Bool.not(from(src, url))
    case False{}:
      rest

# whether the ledger gives this name to a source other than this url. A hub
# dependency of the name is another source too.
def clash(ds: List<&2, M.Dep>, +name: String, +url: String) -> Bool:
  match ds:
    case []:
      False{}
    case h <> t:
      M.Dep{n, _h, _e, s} = h
      clash.at(String.eq(n, name), s, url, clash(t, name, url))

# why a name cannot be recorded, or nothing when it can
def why(ds: List<&2, M.Dep>, +name: String, +url: String) -> String:
  Bool.pick(String, String.is_empty(name),
    "ez: " ++ url ++ " has no name to record it under",
    Bool.pick(String, clash(ds, name, url),
      "ez: ez.toml already has a deps." ++ name ++ " from another source; " ++
        "remove it first, or add this one with --rename",
      ""))

# `--rename`, the way `cargo add --rename` works: when it is given, it is the
# name, ahead of every rule above
def as(ds: List<&2, M.Dep>, +url: String, +rename: String, +pkg: String, +fresh: String) -> String:
  +named = name(ds, url, pkg, fresh)
  Bool.pick(String, String.is_empty(rename), named, rename)

# a `--rename` that can stand as a key, or none at all
def renamed.ok(+rename: String) -> Bool:
  Bool.or(String.is_empty(rename), bare(rename))

# whether a `--rename` gives a second name to a source the ledger already
# records as `old`, "" when it records none
def moved.of(+old: String, +rename: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(rename)),
    Bool.and(Bool.not(String.is_empty(old)), Bool.not(String.eq(old, rename))))

# whether a `--rename` would record a source the ledger already names under a
# second name. That is refused rather than duplicated or silently renamed.
def moved(ds: List<&2, M.Dep>, +url: String, +rename: String) -> Bool:
  moved.of(had(ds, url, ""), rename)

# why a name cannot be recorded when `--rename` may have been given, or
# nothing when it can
def why.as(+ds: List<&2, M.Dep>, +name: String, +url: String, +rename: String) -> String:
  +old = had(ds, url, "")
  +other = why(ds, name, url)
  Bool.pick(String, renamed.ok(rename),
    Bool.pick(String, moved(ds, url, rename),
      "ez: " ++ url ++ " is already recorded as deps." ++ old ++
        "; remove it first to record it as " ++ rename,
      other),
    "ez: --rename " ++ rename ++ " is not a TOML bare key " ++
      "(letters, digits, `-` and `_`)")

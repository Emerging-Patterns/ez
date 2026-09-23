# ez/named: the name `ez add` records a dependency under. A dependency is
# named after where it comes from: a repository by its own name, a directory
# by the directory's. The entry file names nothing, because most packages call
# theirs `main.bend`, and two of them would share one `[deps.main]`. A source
# the ledger already holds keeps the name the ledger gave it, and a name the
# ledger gives to another source is refused rather than written over.
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
        "remove it first, or add this one by hand under another name",
      ""))

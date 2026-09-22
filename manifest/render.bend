# manifest/render: a ledger written back out as ez.toml, and the two edits the
# command line makes to it. Rendering is from the model, so the file it writes
# is the file it would read back.
import Base
import ./manifest.bend as M

# a key line, or nothing at all when the value is empty, so an absent tag,
# entry or bin leaves no trace
def line(key: String, +val: String) -> String:
  Bool.pick(String, String.is_empty(val), "", key ++ " = \"" ++ val ++ "\"\n")

# `true` when the tree is committed, and nothing when it is not, so the key
# is absent rather than written as an empty string
def vendor.word(vend: Bool) -> String:
  match vend:
    case True{}:
      "true"
    case False{}:
      ""

# the keys a source contributes
def source(src: M.Source) -> String:
  match src:
    case M.Hub{}:
      ""
    case M.Git{url, rev, tag, root, nar, vend}:
      line("git", url) ++ line("rev", rev) ++ line("tag", tag) ++
      line("root", root) ++ line("narHash", nar) ++ line("vendor", vendor.word(vend))

# one `[deps.<name>]` section
def dep(dependency: M.Dep) -> String:
  M.Dep{n, h, e, s} = dependency
  "\n[deps." ++ n ++ "]\n" ++ line("hash", h) ++ source(s) ++ line("entry", e)

# every dependency, in the order the ledger holds them
def deps(ds: List<&2, M.Dep>) -> String:
  match ds:
    case []:
      ""
    case h <> t:
      dep(h) ++ deps(t)

# one `[tools.<name>]` section. No hash: a tool is not a package.
def tool(pin: M.Tool) -> String:
  M.Tool{n, e, b, s} = pin
  "\n[tools." ++ n ++ "]\n" ++ source(s) ++ line("entry", e) ++ line("bin", b)

# every pinned CLI, in the order the ledger holds them
def tools(ts: List<&2, M.Tool>) -> String:
  match ts:
    case []:
      ""
    case h <> t:
      tool(h) ++ tools(t)

# the ledger as an ez.toml
def show(manifest: M.Manifest) -> String:
  M.Manifest{n, e, b, h, ds, ts} = manifest
  "[package]\n" ++ line("name", n) ++ line("entry", e) ++ line("bin", b) ++
    line("hub", h) ++ deps(ds) ++ tools(ts)

# a ledger that was read, as an ez.toml; an unreadable one renders as nothing,
# so a failed read can never overwrite a good file with a guess
def render(ledger: M.Read) -> String:
  match ledger:
    case M.Bad{_why}:
      ""
    case M.Good{m}:
      show(m)

# a dependency kept or dropped
def without.put(hit: Bool, dependency: M.Dep, rest: List<&2, M.Dep>) -> List<&2, M.Dep>:
  match hit:
    case True{}:
      rest
    case False{}:
      dependency <> rest

# every dependency but the one named
def without(ds: List<&2, M.Dep>, +name: String) -> List<&2, M.Dep>:
  match ds:
    case []:
      []
    case +h <> t:
      without.put(String.eq(M.dep.name(h), name), h, without(t, name))

# the ledger with a dependency added, replacing any of the same name, so adding
# twice is the same as adding once
def add(manifest: M.Manifest, +dependency: M.Dep) -> M.Manifest:
  M.Manifest{n, e, b, h, ds, ts} = manifest
  M.Manifest{n, e, b, h, List.append(&2, M.Dep, without(ds, M.dep.name(dependency)), [dependency]), ts}

# the ledger with a dependency dropped
def remove(manifest: M.Manifest, name: String) -> M.Manifest:
  M.Manifest{n, e, b, h, ds, ts} = manifest
  M.Manifest{n, e, b, h, without(ds, name), ts}

# a git source with its tree committed
def vendored(src: M.Source) -> M.Source:
  match src:
    case M.Hub{}:
      M.Hub{}
    case M.Git{url, rev, tag, root, nar, _vend}:
      M.Git{url, rev, tag, root, nar, True{}}

# a source that keeps a vendor bit the ledger already set, or is left as given
def revend(keep: Bool, src: M.Source) -> M.Source:
  match keep:
    case True{}:
      vendored(src)
    case False{}:
      src

# a dependency added again keeps the `vendor = true` its entry already had.
# The command line has no way to say it, so a re-add that dropped it would
# drop the tree from the allowlist without anyone having asked.
def readd(ds: List<&2, M.Dep>, dependency: M.Dep) -> M.Dep:
  M.Dep{+n, h, e, s} = dependency
  M.Dep{n, h, e, revend(M.source.vendor(M.source.dep(M.find(ds, n))), s)}

# the ledger with a dependency added, keeping the vendor bit of the entry it
# replaces
def add.keep(manifest: M.Manifest, dependency: M.Dep) -> M.Manifest:
  M.Manifest{n, e, b, h, +ds, ts} = manifest
  add(M.Manifest{n, e, b, h, ds, ts}, readd(ds, dependency))

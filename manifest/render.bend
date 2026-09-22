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
def vendor.word(v: Bool) -> String:
  match v:
    case True{}:
      "true"
    case False{}:
      ""

# the keys a source contributes
def source(s: M.Source) -> String:
  match s:
    case M.Hub{}:
      ""
    case M.Git{url, rev, tag, root, nar, vend}:
      line("git", url) ++ line("rev", rev) ++ line("tag", tag) ++
      line("root", root) ++ line("narHash", nar) ++ line("vendor", vendor.word(vend))

# one `[deps.<name>]` section
def dep(d: M.Dep) -> String:
  M.Dep{n, h, e, s} = d
  "\n[deps." ++ n ++ "]\n" ++ line("hash", h) ++ source(s) ++ line("entry", e)

# every dependency, in the order the ledger holds them
def deps(ds: List<&2, M.Dep>) -> String:
  match ds:
    case []:
      ""
    case h <> t:
      dep(h) ++ deps(t)

# one `[tools.<name>]` section. No hash: a tool is not a package.
def tool(t: M.Tool) -> String:
  M.Tool{n, e, b, s} = t
  "\n[tools." ++ n ++ "]\n" ++ source(s) ++ line("entry", e) ++ line("bin", b)

# every pinned CLI, in the order the ledger holds them
def tools(ts: List<&2, M.Tool>) -> String:
  match ts:
    case []:
      ""
    case h <> t:
      tool(h) ++ tools(t)

# the ledger as an ez.toml
def show(m: M.Manifest) -> String:
  M.Manifest{n, e, b, ds, ts} = m
  "[package]\n" ++ line("name", n) ++ line("entry", e) ++ line("bin", b) ++
    deps(ds) ++ tools(ts)

# a ledger that was read, as an ez.toml; an unreadable one renders as nothing,
# so a failed read can never overwrite a good file with a guess
def render(r: M.Read) -> String:
  match r:
    case M.Bad{_why}:
      ""
    case M.Good{m}:
      show(m)

# a dependency kept or dropped
def without.put(hit: Bool, d: M.Dep, rest: List<&2, M.Dep>) -> List<&2, M.Dep>:
  match hit:
    case True{}:
      rest
    case False{}:
      d <> rest

# every dependency but the one named
def without(ds: List<&2, M.Dep>, +name: String) -> List<&2, M.Dep>:
  match ds:
    case []:
      []
    case +h <> t:
      without.put(String.eq(M.dep.name(h), name), h, without(t, name))

# the ledger with a dependency added, replacing any of the same name, so adding
# twice is the same as adding once
def add(m: M.Manifest, +d: M.Dep) -> M.Manifest:
  M.Manifest{n, e, b, ds, ts} = m
  M.Manifest{n, e, b, List.append(&2, M.Dep, without(ds, M.dep.name(d)), [d]), ts}

# the ledger with a dependency dropped
def remove(m: M.Manifest, name: String) -> M.Manifest:
  M.Manifest{n, e, b, ds, ts} = m
  M.Manifest{n, e, b, without(ds, name), ts}

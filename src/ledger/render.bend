# ledger/render: a ledger written back out as ez.toml, and the two edits the
# command line makes to it. Rendering is from the model, so the file it writes
# is the file it would read back.
import Base
import ./manifest.bend as M
import ../toml/toml.bend as T

# a key line, or nothing at all when the value is empty, so an absent tag,
# entry or bin leaves no trace
def line(key: String, +val: String) -> String:
  Bool.pick(String, String.is_empty(val), "", key ++ " = \"" ++ val ++ "\"\n")

# a key line whose value is written bare, as a TOML boolean is, or nothing at
# all when the value is empty
def line.bare(key: String, +val: String) -> String:
  Bool.pick(String, String.is_empty(val), "", key ++ " = " ++ val ++ "\n")

# `true` when the tree is committed, and nothing when it is not, so the key
# is absent rather than written as an empty string. It is written bare: in
# TOML `vendor = "true"` is a string, and a reader other than ez, such as
# nix's `builtins.fromTOML`, would take it for one. ez reads both spellings.
def vendor.word(vend: Bool) -> String:
  match vend:
    case True{}:
      "true"
    case False{}:
      ""

# the keys a source contributes
def source(src: M.Source) -> String:
  match src:
    case M.Hub{named}:
      line("hub", named)
    case M.Git{url, rev, tag, root, nar, vend}:
      line("git", url) ++ line("rev", rev) ++ line("tag", tag) ++
      line("root", root) ++ line("narHash", nar) ++ line.bare("vendor", vendor.word(vend))

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

# the ledger as ez assembles it, in the TOML ez wrote before eztoml 0.4
def text(manifest: M.Manifest) -> String:
  M.Manifest{n, e, b, h, pa, pv, ds, ts} = manifest
  "[package]\n" ++ line("name", n) ++ line("entry", e) ++ line("bin", b) ++
    line("hub", h) ++ line("publish-as", pa) ++ line("version", pv) ++
    deps(ds) ++ tools(ts)

# the ledger as an ez.toml: ez's text, written as eztoml writes it
def show(manifest: M.Manifest) -> String:
  T.normal(text(manifest))

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
  M.Manifest{n, e, b, h, pa, pv, ds, ts} = manifest
  M.Manifest{n, e, b, h, pa, pv, List.append(&2, M.Dep, without(ds, M.dep.name(dependency)), [dependency]), ts}

# the ledger with a dependency dropped
def remove(manifest: M.Manifest, name: String) -> M.Manifest:
  M.Manifest{n, e, b, h, pa, pv, ds, ts} = manifest
  M.Manifest{n, e, b, h, pa, pv, without(ds, name), ts}

# a git source with its tree committed
def vendored(src: M.Source) -> M.Source:
  match src:
    case M.Hub{named}:
      M.Hub{named}
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
  M.Manifest{n, e, b, h, pa, pv, +ds, ts} = manifest
  add(M.Manifest{n, e, b, h, pa, pv, ds, ts}, readd(ds, dependency))

# ---------------------------------------------------------------------------
# what a ledger may hold to be written

# whether a text holds no copy of a char
def clear(text: String, +ch: Char) -> Bool:
  match text:
    case SNil{}:
      True{}
    case SCon{h, t}:
      rest = clear(t, ch)
      Bool.and(Bool.not(Char.is_eq(h, ch)), rest)

# whether a name or value can be written as it is: it holds no `"`, no `\`
# and no newline. The pinned eztoml reader (v0.1.0) neither writes nor reads
# escapes, a newline would end the line, and a quote or a backslash would make
# the file mean something else to every other TOML reader, nix's among them.
def clean(+text: String) -> Bool:
  Bool.and(clear(text, '"'), Bool.and(clear(text, '\\'), clear(text, '\n')))

# whether a source reads back as itself. A git source names its repo and the
# directory its paths are written from: the reader takes a section with no
# `git` for a hub package and one with no `root` for the top of the checkout.
def source.ok(src: M.Source) -> Bool:
  match src:
    case M.Hub{+named}:
      clean(named)
    case M.Git{+url, rev, tag, +root, nar, _vend}:
      Bool.and(Bool.and(Bool.not(String.is_empty(url)), Bool.not(String.is_empty(root))),
        Bool.and(Bool.and(clean(url), clean(rev)),
          Bool.and(clean(tag), Bool.and(clean(root), clean(nar)))))

# whether a dependency does: it has a hash, which the reader asks every
# dependency for, and every name and value is clean
def dep.ok(dependency: M.Dep) -> Bool:
  M.Dep{+n, +h, +e, s} = dependency
  Bool.and(Bool.and(clean(n), Bool.and(Bool.not(String.is_empty(h)), clean(h))),
    Bool.and(clean(e), source.ok(s)))

# whether every dependency does
def deps.ok(ds: List<&2, M.Dep>) -> Bool:
  match ds:
    case []:
      True{}
    case h <> t:
      rest = deps.ok(t)
      Bool.and(dep.ok(h), rest)

# whether a pinned CLI's source does. A tool is never imported, so the reader
# keeps no hub name for one, and one written with a name would read back
# without it.
def tool.src.ok(src: M.Source) -> Bool:
  match src:
    case M.Hub{named}:
      String.is_empty(named)
    case M.Git{url, rev, tag, root, nar, vend}:
      source.ok(M.Git{url, rev, tag, root, nar, vend})

# whether a pinned CLI does
def tool.ok(pin: M.Tool) -> Bool:
  M.Tool{+n, +e, +b, s} = pin
  Bool.and(clean(n), Bool.and(Bool.and(clean(e), clean(b)), tool.src.ok(s)))

# whether every pinned CLI does
def tools.ok(ts: List<&2, M.Tool>) -> Bool:
  match ts:
    case []:
      True{}
    case h <> t:
      rest = tools.ok(t)
      Bool.and(tool.ok(h), rest)

# whether a ledger can be written so that it reads back as itself (EZ-LED-4):
# every name and value is clean, `publish-as` and `version` among them, every
# dependency has a hash, and every git source names its repo and its root.
# Every command that writes ez.toml refuses a ledger that is not, so every
# ledger ez writes is one of these.
def renderable(manifest: M.Manifest) -> Bool:
  M.Manifest{+n, +e, +b, +h, +pa, +pv, ds, ts} = manifest
  Bool.and(Bool.and(Bool.and(clean(n), clean(e)), Bool.and(clean(b), clean(h))),
    Bool.and(Bool.and(clean(pa), clean(pv)), Bool.and(deps.ok(ds), tools.ok(ts))))

# why a ledger that is not renderable is not written
def unrenderable() -> String:
  "ez: ez.toml cannot be written: a name or value holds a quote, a backslash or a newline, a dependency has no hash, or a git source names no repo or no root"

# ezx: ez's ledger library for Bend 2: it parses an ez.toml into its package, dependencies and pinned tools.
#
# main: the library's entry, which the hub publishes as ezx. It names the
# reading ledger/manifest.bend does, one def each, so a program can read a
# ledger by importing this file alone; the types the answers come in are
# ledger/manifest.bend's, and a program that takes one apart imports that
# file too. It sits at the top of the repo so the LICENSE beside it goes
# along with the package. The ez binary is ez/main.bend, which ez.toml names
# as `bin`.
import Base
import ./ledger/manifest.bend as M

# an ez.toml's text read as a ledger, or why it could not be
def parse(text: String) -> M.Read:
  M.parse(text)

# a ledger, or the error, on one line
def show(ledger: M.Read) -> String:
  M.show(ledger)

# the named dependency of a ledger, or one with empty fields
def dep(ledger: M.Read, name: String) -> M.Dep:
  M.dep(ledger, name)

# a dependency's own name
def dep.name(dependency: M.Dep) -> String:
  M.dep.name(dependency)

# a dependency's hash, the `0x` name its import line carries
def dep.hash(dependency: M.Dep) -> String:
  M.dep.hash(dependency)

# the file inside the package a dependency was added by
def dep.entry(dependency: M.Dep) -> String:
  M.dep.entry(dependency)

# where a dependency's bytes come from
def dep.source(dependency: M.Dep) -> M.Source:
  M.source.dep(dependency)

# the commit a source is pinned to, or "" for a hub package
def source.rev(src: M.Source) -> String:
  M.source.rev(src)

# the tag a source was asked for, or "" when it was pinned by commit
def source.tag(src: M.Source) -> String:
  M.source.tag(src)

# the repo a source is taken from, or "" for a hub package
def source.url(src: M.Source) -> String:
  M.source.url(src)

# the `<name>@<version>` a hub source was added by, or ""
def source.nv(src: M.Source) -> String:
  M.source.nv(src)

# whether a source names a repo rather than the hub
def source.is_git(src: M.Source) -> Bool:
  M.source.is_git(src)

# the commit the named dependency is pinned to
def rev_of(ledger: M.Read, name: String) -> String:
  M.rev_of(ledger, name)

# the tag the named dependency was asked for
def tag_of(ledger: M.Read, name: String) -> String:
  M.tag_of(ledger, name)

# the hub a ledger's packages come from
def hub_of(ledger: M.Read) -> String:
  M.hub_of(ledger)

# the pinned CLIs of a ledger
def tools_of(ledger: M.Read) -> List<&2, M.Tool>:
  M.tools_of(ledger)

# a tool's own name
def tool.name(pin: M.Tool) -> String:
  M.tool.name(pin)

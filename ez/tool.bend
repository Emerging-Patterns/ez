# ez/tool: `ez tool sync`, `ez tool run`, `ez tool install`, `ez tool upgrade`,
# and `ezx`. A target is resolved, its ledger read, its lock fetched, and the
# binary it names built under `$XDG_CACHE_HOME/ez/tool/<slug>`
# (`~/.cache/ez/tool/<slug>` when that variable is unset). A name that matches
# a `[tools.*]` pin is built at the rev in `ez.lock.toml`. Any other target is
# resolved as a free `owner/repo`, URL or path.
#
# A remote is cloned again only when `git ls-remote <url> HEAD` names a
# different commit than the `rev` file, and the binary is built again only
# when that commit changed or the binary is not there. A path uses a clean
# `HEAD`; a dirty worktree, or a directory that is not a checkout, has no
# commit and is built every time. `run` then starts the binary and takes
# its status. `install` and `upgrade` do not run it. Both link the built
# file onto PATH under the package's name: `$EZ_TOOL_BIN` when that is
# set, otherwise `$XDG_BIN_HOME`, otherwise `~/.local/bin`. `upgrade` reads
# the commit again, leaves a binary already built from it in place, rebuilds
# a commit that moved, and writes the link either way. A target, ledger,
# fetch, build or link that fails exits 1.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../git/git.bend as Git
import ../lock/restore.bend as Restore
import ../pkg/path.bend as P
import ../manifest/manifest.bend as M
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./cap.bend as Cap
import ./env.bend as Env
import ./target.bend as Tgt
import ../ez/say.bend as Say

# what happens once the binary for this commit is in the cache. `Run`
# starts it. `Install` and `Upgrade` link it and say where.
type Act is Data:
  Run{args: List<&2, String>}
  Install{}
  Upgrade{}

# the first line, or nothing
def line0(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{h, _t}:
      h

# the field before the tab
def sha.field(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{h, _t}:
      String.trim(h)

# the commit `git ls-remote` printed
def sha.of(+line: String) -> String:
  sha.field(String.split(line, '\t'))

# a commit, or a refusal when the remote named none
def head.got(empty: Bool, +sha: String, +url: String) -> IO(String):
  match empty:
    case True{}:
      IO.die(String, 1, "ez: " ++ url ++ " has no HEAD")
    case False{}:
      IO.pure(String, sha)

# a line that named a commit
def head.ok(+url: String, +text: String) -> IO(String):
  +sha = sha.of(line0(String.lines(text)))
  head.got(String.is_empty(sha), sha, url)

# what ls-remote answered
def head.said(ok: Bool, +url: String, +text: String) -> IO(String):
  match ok:
    case False{}:
      IO.die(String, 1, "ez: git ls-remote " ++ url ++ ": " ++ text)
    case True{}:
      head.ok(url, text)

# the commit a remote's HEAD names
def head.ask(+url: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["git", "ls-remote", url, "HEAD"])
    head.said(R.ok(out), url, R.text(out))

# a file's text, trimmed, or "" when there is no file
def text(+path: String) -> IO(String):
  do IO<String>:
    m : Maybe<&2, String> <- F.read(path)
    return String.trim(F.text_of(m))

# whether a command exited 0
def ran(args: List<&2, String>) -> IO(Bool):
  do IO<Bool>:
    +out : String <- R.exec(args)
    return R.ok(out)

# whether a file is there
def is.file(+path: String) -> IO(Bool):
  ran(["test", "-f", path])

# whether a binary is there and executable
def is.exec(+path: String) -> IO(Bool):
  ran(["test", "-x", path])

# an absolute path, or the reason realpath gave
def abs.said(ok: Bool, +path: String, +text: String) -> IO(String):
  match ok:
    case False{}:
      IO.die(String, 1, "ez: " ++ path ++ ": " ++ String.trim(text))
    case True{}:
      IO.pure(String, String.trim(text))

# the path a local target names, with `~` already expanded
def abs.of(+path: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["realpath", path])
    abs.said(R.ok(out), path, R.text(out))

# the cache root. `XDG_CACHE_HOME` wins; otherwise `~/.cache`.
def cache.home(no_home: Bool, +home: String) -> IO(String):
  match no_home:
    case True{}:
      IO.die(String, 1, "ez: HOME is unset, so there is no cache")
    case False{}:
      IO.pure(String, home ++ "/.cache/ez/tool")

def cache.pick(no_xdg: Bool, +xdg: String, +home: String) -> IO(String):
  match no_xdg:
    case False{}:
      IO.pure(String, xdg ++ "/ez/tool")
    case True{}:
      cache.home(String.is_empty(home), home)

def cache.root() -> IO(String):
  do IO<String>:
    +xdg : String <- Env.var("XDG_CACHE_HOME", "")
    +home : String <- Env.var("HOME", "")
    cache.pick(String.is_empty(xdg), xdg, home)

# `~/.local/bin`, when HOME is set
def bin.home(no_home: Bool, +home: String) -> IO(String):
  match no_home:
    case True{}:
      IO.die(String, 1, "ez: HOME is unset, so there is no bin directory")
    case False{}:
      IO.pure(String, home ++ "/.local/bin")

# `XDG_BIN_HOME` when it is set, otherwise `~/.local/bin`
def bin.xdg(no_xdg: Bool, +xdg: String, +home: String) -> IO(String):
  match no_xdg:
    case False{}:
      IO.pure(String, xdg)
    case True{}:
      bin.home(String.is_empty(home), home)

# `EZ_TOOL_BIN` when it is set, otherwise the bin home above
def bin.pick(no_ez: Bool, +ez: String, +xdg: String, +home: String) -> IO(String):
  match no_ez:
    case False{}:
      IO.pure(String, ez)
    case True{}:
      bin.xdg(String.is_empty(xdg), xdg, home)

# where an installed command is linked
def bin.dir() -> IO(String):
  do IO<String>:
    +ez : String <- Env.var("EZ_TOOL_BIN", "")
    +xdg : String <- Env.var("XDG_BIN_HOME", "")
    +home : String <- Env.var("HOME", "")
    bin.pick(String.is_empty(ez), ez, xdg, home)

# one trailing slash is the same directory
def bare.go(slash: Bool, +dir: String) -> String:
  match slash:
    case True{}:
      String.take(dir, Nat.sub(String.length(dir), 1n))
    case False{}:
      dir

# a directory with no trailing slash
def bare(+dir: String) -> String:
  bare.go(String.ends_with(dir, "/"), dir)

# one step of a scan that may stop at the first hit. `Bool.or` reduces both
# sides, so the rest arrives as a thunk.
def seen.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# whether this directory is one of the entries
def seen(+dir: String, ps: List<&2, String>) -> Bool:
  match ps:
    case []:
      False{}
    case +h <> t:
      seen.step(String.eq(bare(h), bare(dir)), _u => seen(dir, t))

# whether `dir` is an entry of `PATH`
def on.path(+dir: String, +path: String) -> Bool:
  seen(dir, String.split(path, ':'))

# a link that did not happen is a failure, and a directory that PATH does
# not name is said once, the way a missing cap is
def place.warn(there: Bool, +dir: String) -> IO(Unit):
  match there:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.write("warning: " ++ dir ++ " is not on PATH\n")

def place.after(ok: Bool, +at: String, +text: String, +dir: String) -> IO(Unit):
  match ok:
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ ": " ++ String.trim(text))
    case True{}:
      do IO<Unit>:
        +path : String <- Env.var("PATH", "")
        place.warn(on.path(dir, path), dir)

# the absolute binary linked under `name` in this directory. The path is
# what the next line reports.
def place.at(+dir: String, +bin: String, +name: String) -> IO(String):
  +at = dir ++ "/" ++ name
  do IO<String>:
    IO.print_err(Say.linking(at))
    _mk : String <- R.exec(["mkdir", "-p", dir])
    +ln : String <- R.exec(["ln", "-sfn", bin, at])
    place.after(R.ok(ln), at, R.text(ln), dir)
    return at

# the built file linked as the package's name. The link names the absolute
# path, so it does not depend on the directory the command is run from.
def place(+out: String, +name: String) -> IO(String):
  do IO<String>:
    +dir : String <- bin.dir()
    +bin : String <- abs.of(out)
    place.at(dir, bin, name)

# the same commit, and a commit at all. An empty rev is a dirty tree or a
# directory that is not a git checkout, and those are built every time.
def same(+cached: String, +rev: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(rev)), String.eq(cached, rev))

# the binary already built for this commit
def reuse(+cached: String, +rev: String, bin_ok: Bool) -> Bool:
  Bool.and(bin_ok, same(cached, rev))

# the checkout is already this commit
def fresh(src_ok: Bool, +cached: String, +rev: String) -> Bool:
  Bool.and(src_ok, same(cached, rev))

# a write that did not happen is a failure
def wrote(ok: Bool, +at: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " could not be written")

# the rev file, written after a build that used this commit. Empty when the
# tree was dirty, so the next clean commit cannot reuse a dirty binary.
def stamp(+at: String, +rev: String) -> IO(Unit):
  do IO<Unit>:
    ok : Bool <- F.write(at, rev ++ "\n")
    wrote(ok, at)

# a lock that is not there cannot be fetched
def fetch.gone(+src: String) -> IO(Unit):
  IO.die(Unit, 1, "ez: " ++ src ++ " has no ez.lock.toml")

# the lock's text, fetched into `lib`
def fetch.go(got: Maybe<&2, String>, +src: String, +lib: String) -> IO(Unit):
  match got:
    case None{}:
      fetch.gone(src)
    case Some{body}:
      Restore.restore.at(T.sects(T.parse(body)), lib)

# BEND_LIB filled from the checkout's lock
def fetch(+src: String, +lib: String) -> IO(Unit):
  do IO<Unit>:
    m : Maybe<&2, String> <- F.read(src ++ "/ez.lock.toml")
    fetch.go(m, src, lib)

# a build's output, kept when it failed. A success says nothing: the
# program's own output follows.
def compile.said(ok: Bool, +why: String, +text: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      do IO<Unit>:
        IO.write(why ++ text)
        IO.die(Unit, 1, "")

# `bend <entry> -o <out>` under the memory cap, with this checkout's library
def compile(+lib: String, +entry: String, +out: String) -> IO(Unit):
  do IO<Unit>:
    +on : Bool <- Cap.ok()
    Cap.warn(on)
    +g : String <- Cap.gb()
    _mk : String <- R.exec(["mkdir", "-p", P.dir(out)])
    +bin : String <- R.exec(Cap.argv(on, g, lib, ["bend", entry, "-o", out]))
    compile.said(R.ok(bin), Cap.why(bin, g), R.text(bin))

# a status that parsed. Zero is success; anything else is that status.
def code.die(zero: Bool, status: U32) -> IO(Unit):
  match zero:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, status, "")

# the program's status, forwarded. A status that is not a number exits 1.
def code.of(exit: Maybe<&2, U32>) -> IO(Unit):
  match exit:
    case None{}:
      IO.die(Unit, 1, "")
    case Some{+n}:
      code.die(U32.is_eq(n, 0), n)

# the binary, with the words that followed the target
def launch(+bin: String, args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(List.append(&2, String, [bin], args))
    IO.write(R.text(out))
    code.of(U32.read(R.code(out)))

def finish.said(install: Bool, +name: String, +at: String) -> IO(Unit):
  match install:
    case True{}:
      IO.print_err(Say.installed(name, at))
    case False{}:
      IO.print_err(Say.linked(name, at))

# the link, then the line that names it
def finish.link(which: Bool, +out: String, +name: String) -> IO(Unit):
  do IO<Unit>:
    +at : String <- place(out, name)
    finish.said(which, name, at)

# the binary, once it is current. Install and upgrade link it and stop.
def finish(act: Act, +out: String, +name: String) -> IO(Unit):
  match act:
    case Install{}:
      finish.link(True{}, out, name)
    case Upgrade{}:
      finish.link(False{}, out, name)
    case Run{args}:
      launch(out, args)

# a checkout with no ledger
def load.missing(+src: String) -> IO(M.Read):
  IO.die(M.Read, 1, "ez: " ++ src ++ "/ez.toml is not there")

# the file, or a refusal when it is not there
def load.go(got: Maybe<&2, String>, +src: String) -> IO(M.Read):
  match got:
    case None{}:
      load.missing(src)
    case Some{body}:
      IO.pure(M.Read, M.parse(body))

# the ledger read out of a checkout
def load(+src: String) -> IO(M.Read):
  do IO<M.Read>:
    m : Maybe<&2, String> <- F.read(src ++ "/ez.toml")
    load.go(m, src)

# a commit that is HEAD when the worktree is clean, and "" when it is dirty
# or not a checkout. "" is never equal to a stored rev, so a dirty tree is
# built every time and never stored as a commit.
def local.sha(head_ok: Bool, st_ok: Bool, +sha: String, +dirty: String) -> String:
  Bool.pick(String,
    Bool.and(head_ok, Bool.and(st_ok, String.is_empty(dirty))), sha, "")

def local.rev(+path: String) -> IO(String):
  do IO<String>:
    +head : String <- R.exec(["git", "-C", path, "rev-parse", "HEAD"])
    +st : String <- R.exec(["git", "-C", path, "status", "--porcelain"])
    return local.sha(R.ok(head), R.ok(st), String.trim(R.text(head)),
      String.trim(R.text(st)))

# fetch, build, record the commit, then start the binary or link it
def miss(
  +src: String,
  +lib: String,
  +entry: String,
  +out: String,
  +dir: String,
  +rev: String,
  +name: String,
  act: Act
) -> IO(Unit):
  do IO<Unit>:
    fetch(src, lib)
    +s : Say.Spin <- Say.hold(Say.building(name))
    compile(lib, entry, out)
    Say.done(s)
    stamp(dir ++ "/rev", rev)
    finish(act, out, name)

# the binary when it is already this commit, otherwise a build
def go.hit(
  hit: Bool,
  +src: String,
  +lib: String,
  +entry: String,
  +out: String,
  +dir: String,
  +rev: String,
  +name: String,
  act: Act
) -> IO(Unit):
  match hit:
    case True{}:
      do IO<Unit>:
        IO.print_err(Say.reused(name))
        finish(act, out, name)
    case False{}:
      miss(src, lib, entry, out, dir, rev, name, act)

# the package's name and file, then the cached binary
def go.named(
  +name: String,
  +entry: String,
  +src: String,
  +lib: String,
  +dir: String,
  +rev: String,
  act: Act
) -> IO(Unit):
  +out = dir ++ "/bin/" ++ name ++ ".out"
  do IO<Unit>:
    +cached : String <- text(dir ++ "/rev")
    +bin_ok : Bool <- is.exec(out)
    go.hit(reuse(cached, rev, bin_ok), src, lib, entry, out, dir, rev, name, act)

# the file a pin names, or the checkout's own file when the pin names none.
# An empty pin is "", not `main.bend`: that default belongs to the checkout.
def go.over(empty: Bool, +over: String, +binary: String, +entry: String) -> String:
  match empty:
    case True{}:
      Tgt.file.of(binary, entry)
    case False{}:
      over

# a ledger that read. `over` is a file the pin named, or "" for the checkout's.
def go.good(
  manifest: M.Manifest,
  +src: String,
  +lib: String,
  +dir: String,
  +rev: String,
  act: Act,
  +over: String
) -> IO(Unit):
  M.Manifest{+n, +e, +b, _ds, _ts} = manifest
  go.named(Tgt.out.name(n), P.join(src, go.over(String.is_empty(over), over, b, e)),
    src, lib, dir, rev, act)

# the ledger, or the reason it did not read
def go.read(
  ledger: M.Read,
  +src: String,
  +lib: String,
  +dir: String,
  +rev: String,
  act: Act,
  +over: String
) -> IO(Unit):
  match ledger:
    case M.Bad{why}:
      IO.die(Unit, 1, "ez: error: " ++ why)
    case M.Good{m}:
      go.good(m, src, lib, dir, rev, act, over)

# the checkout's ledger, built into `dir`. `Run` starts the binary.
def go(+src: String, +lib: String, +dir: String, +rev: String, act: Act, +over: String) -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load(src)
    go.read(r, src, lib, dir, rev, act, over)

# a checkout replaced with this commit. The rev file is left alone until the
# build has written a binary for it.
def clone(+src: String, +url: String, +rev: String, +label: String) -> IO(Unit):
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", src])
    Git.clone.say(src, url, rev, Say.fetching(label, rev))

# clone when the checkout is not already this commit
def freshen(need: Bool, +src: String, +url: String, +rev: String, +label: String) -> IO(Unit):
  match need:
    case False{}:
      IO.print_err(Say.kept(label))
    case True{}:
      clone(src, url, rev, label)

# the checkout and the binary for one remote, once the cache root and the
# commit are known
def run.remote.at(+root: String, +url: String, +slug: String, +rev: String, act: Act, +over: String) -> IO(Unit):
  +dir = root ++ "/" ++ slug
  +src = dir ++ "/src"
  do IO<Unit>:
    +cached : String <- text(dir ++ "/rev")
    +src_ok : Bool <- is.file(src ++ "/ez.toml")
    freshen(Bool.not(fresh(src_ok, cached, rev)), src, url, rev, slug)
    go(src, src ++ "/.ez/lib", dir, rev, act, over)

# a remote: the cache holds the checkout and the binary
def run.remote(+url: String, +slug: String, act: Act) -> IO(Unit):
  do IO<Unit>:
    +root : String <- cache.root()
    +s : Say.Spin <- Say.hold(Say.resolving.at(slug))
    +rev : String <- head.ask(url)
    Say.done(s)
    run.remote.at(root, url, slug, rev, act, "")

# a path, once it is absolute and its commit is known
def run.local.at(+root: String, +abs: String, +rev: String, act: Act) -> IO(Unit):
  +dir = root ++ "/local" ++ abs
  go(abs, dir ++ "/lib", dir, rev, act, "")

# a path: nothing is cloned. Dependencies are fetched into the cache, not
# into the tree.
def run.local(+path: String, act: Act) -> IO(Unit):
  do IO<Unit>:
    +home : String <- Env.var("HOME", "")
    +abs : String <- abs.of(Tgt.expand(home, path))
    +root : String <- cache.root()
    +rev : String <- local.rev(abs)
    run.local.at(root, abs, rev, act)

# a target that did not resolve
def run.bad(+why: String) -> IO(Unit):
  IO.die(Unit, 1, "ez: " ++ why)

# a classified target
def run.go(target: Tgt.Place, act: Act) -> IO(Unit):
  match target:
    case Tgt.Bad{why}:
      run.bad(why)
    case Tgt.Local{path}:
      run.local(path, act)
    case Tgt.Remote{url, slug}:
      run.remote(url, slug, act)

# a ledger that did not parse stops the command
def project.read(ledger: M.Read) -> IO(M.Read):
  match ledger:
    case M.Bad{why}:
      IO.die(M.Read, 1, "ez: error: " ++ why)
    case M.Good{_m}:
      IO.pure(M.Read, ledger)

# a missing ledger pins nothing, so the word stays a free target
def project.go(got: Maybe<&2, String>) -> IO(M.Read):
  match got:
    case None{}:
      IO.pure(M.Read, M.Good{M.Manifest{"", "", "", [], []}})
    case Some{body}:
      project.read(M.parse(body))

# the project's own ledger
def project() -> IO(M.Read):
  do IO<M.Read>:
    m : Maybe<&2, String> <- F.read("ez.toml")
    project.go(m)

# the lock's text, or a refusal when it was not written
def lock.open(got: Maybe<&2, String>) -> IO(String):
  match got:
    case None{}:
      IO.die(String, 1, "ez: ez.lock.toml is not there")
    case Some{body}:
      IO.pure(String, body)

# a name the lock does not pin
def lock.have(missing: Bool, +name: String, tool: M.Tool) -> IO(M.Tool):
  match missing:
    case True{}:
      IO.die(M.Tool, 1, "ez: " ++ name ++ " is not pinned in ez.lock.toml")
    case False{}:
      IO.pure(M.Tool, tool)

# the pin `ez lock` wrote for this name
def locked(+name: String) -> IO(M.Tool):
  do IO<M.Tool>:
    m : Maybe<&2, String> <- F.read("ez.lock.toml")
    +body : String <- lock.open(m)
    +t : M.Tool <- IO.pure(M.Tool,
      M.tool.find(M.tools(T.sects(T.parse(body))), name))
    lock.have(String.is_empty(M.tool.name(t)), name, t)

# `bin` when the pin names one, otherwise `entry`, otherwise "" so the
# checkout's own ledger chooses the file
def over.of(+binary: String, +entry: String) -> String:
  Bool.pick(String, String.is_empty(binary), entry, binary)

# a pin with no commit cannot be built
def pinned.rev(empty: Bool, +name: String, +rev: String) -> IO(String):
  match empty:
    case True{}:
      IO.die(String, 1, "ez: tools." ++ name ++ " has no rev")
    case False{}:
      IO.pure(String, rev)

# a classified git url, built at the rev the lock recorded
def pinned.place(target: Tgt.Place, +rev: String, +over: String, act: Act) -> IO(Unit):
  match target:
    case Tgt.Bad{why}:
      IO.die(Unit, 1, "ez: " ++ why)
    case Tgt.Local{_path}:
      IO.die(Unit, 1, "ez: a pinned tool names a git repo")
    case Tgt.Remote{url, slug}:
      do IO<Unit>:
        +root : String <- cache.root()
        run.remote.at(root, url, slug, rev, act, over)

# one pinned CLI, at the lock rev rather than at HEAD
def run.pinned(+tool: M.Tool, act: Act) -> IO(Unit):
  +src = M.tool.source(tool)
  +name = M.tool.name(tool)
  do IO<Unit>:
    +rev : String <- pinned.rev(String.is_empty(M.source.rev(src)), name,
      M.source.rev(src))
    pinned.place(Tgt.classify(M.source.url(src)), rev,
      over.of(M.tool.bin(tool), M.tool.entry(tool)), act)

# a manifest name is that pin; any other word is a free target
def named.go(free: Bool, +target: String, act: Act) -> IO(Unit):
  match free:
    case True{}:
      run.go(Tgt.classify(target), act)
    case False{}:
      do IO<Unit>:
        +pin : M.Tool <- locked(target)
        run.pinned(pin, act)

# a word run as the pin the ledger gives it, or as a free target
def named(+target: String, act: Act) -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- project()
    +t : M.Tool <- IO.pure(M.Tool, M.tool.find(M.tools_of(r), target))
    named.go(String.is_empty(M.tool.name(t)), target, act)

# every pinned CLI, built and linked at its lock rev
def sync.go(ts: List<&2, M.Tool>) -> IO(Unit):
  match ts:
    case []:
      IO.pure(Unit, Unit{})
    case +h <> t:
      do IO<Unit>:
        +pin : M.Tool <- locked(M.tool.name(h))
        run.pinned(pin, Install{})
        sync.go(t)

# `ez tool sync`
def sync() -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- project()
    sync.go(M.tools_of(r))

# `ez tool run <target> [-- args…]`, and what `ezx` runs. A name that is a
# `[tools.*]` pin is built at the lock rev. Anything else is a free target.
def run(+target: String, args: List<&2, String>) -> IO(Unit):
  named(target, Run{args})

# `ez tool install <target>`: the lock fetched, the binary built, linked
# onto PATH under the package's name, not run
def install(+target: String) -> IO(Unit):
  named(target, Install{})

# `ez tool upgrade <target>`: the same resolution `run` uses, and a rebuild
# when that commit is not the one on record. A pinned tool uses the lock rev.
# The PATH link is written again. The binary is not run.
def upgrade(+target: String) -> IO(Unit):
  named(target, Upgrade{})

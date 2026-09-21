# ez/tool: `ez tool run`, `ez tool install`, `ez tool upgrade`, and `ezx`.
# A target is resolved, its ledger read, its lock fetched, and the binary
# it names built under `$XDG_CACHE_HOME/ez/tool/<slug>`
# (`~/.cache/ez/tool/<slug>` when that variable is unset).
#
# A remote is cloned again only when `git ls-remote <url> HEAD` names a
# different commit than the `rev` file, and the binary is built again only
# when that commit changed or the binary is not there. A path uses a clean
# `HEAD`; a dirty worktree, or a directory that is not a checkout, has no
# commit and is built every time. `run` then starts the binary and takes
# its status. `install` stops once the binary is there. `upgrade` is that
# same resolution: the commit is read again, a binary already built from
# it is left in place, and a commit that moved is rebuilt. Neither runs
# the binary. A target, ledger, fetch or build that fails exits 1.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ../git/git.bend as Git
import ../lock/restore.bend as Restore
import ../pkg/path.bend as P
import ../manifest/manifest.bend as M
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ./cap.bend as Cap
import ./env.bend as Env
import ./target.bend as Tgt

# what happens once the binary for this commit is in the cache. `Run`
# starts it. `Hold` is `install` and `upgrade`: the binary stays put.
type Act is Data:
  Run{args: List<&2, String>}
  Hold{}

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
def fetch.go(m: Maybe<&2, String>, +src: String, +lib: String) -> IO(Unit):
  match m:
    case None{}:
      fetch.gone(src)
    case Some{text}:
      Restore.restore.at(T.sects(T.parse(text)), lib)

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
def code.die(zero: Bool, n: U32) -> IO(Unit):
  match zero:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, n, "")

# the program's status, forwarded. A status that is not a number exits 1.
def code.of(m: Maybe<&2, U32>) -> IO(Unit):
  match m:
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

# the binary, once it is current. Install and upgrade stop here.
def finish(act: Act, +out: String) -> IO(Unit):
  match act:
    case Hold{}:
      IO.pure(Unit, Unit{})
    case Run{args}:
      launch(out, args)

# a checkout with no ledger
def load.missing(+src: String) -> IO(M.Read):
  IO.die(M.Read, 1, "ez: " ++ src ++ "/ez.toml is not there")

# the file, or a refusal when it is not there
def load.go(m: Maybe<&2, String>, +src: String) -> IO(M.Read):
  match m:
    case None{}:
      load.missing(src)
    case Some{text}:
      IO.pure(M.Read, M.parse(text))

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

# fetch, build, record the commit, then start the binary or stop
def miss(+src: String, +lib: String, +entry: String, +out: String,
  +dir: String, +rev: String, act: Act) -> IO(Unit):
  do IO<Unit>:
    fetch(src, lib)
    compile(lib, entry, out)
    stamp(dir ++ "/rev", rev)
    finish(act, out)

# the binary when it is already this commit, otherwise a build
def go.hit(hit: Bool, +src: String, +lib: String, +entry: String, +out: String,
  +dir: String, +rev: String, act: Act) -> IO(Unit):
  match hit:
    case True{}:
      finish(act, out)
    case False{}:
      miss(src, lib, entry, out, dir, rev, act)

# the package's name and file, then the cached binary
def go.named(+name: String, +entry: String, +src: String, +lib: String,
  +dir: String, +rev: String, act: Act) -> IO(Unit):
  +out = dir ++ "/bin/" ++ name ++ ".out"
  do IO<Unit>:
    +cached : String <- text(dir ++ "/rev")
    +bin_ok : Bool <- is.exec(out)
    go.hit(reuse(cached, rev, bin_ok), src, lib, entry, out, dir, rev, act)

# a ledger that read
def go.good(m: M.Manifest, +src: String, +lib: String, +dir: String,
  +rev: String, act: Act) -> IO(Unit):
  M.Manifest{+n, +e, +b, _ds} = m
  go.named(Tgt.out.name(n), P.join(src, Tgt.file.of(b, e)), src, lib, dir,
    rev, act)

# the ledger, or the reason it did not read
def go.read(r: M.Read, +src: String, +lib: String, +dir: String, +rev: String,
  act: Act) -> IO(Unit):
  match r:
    case M.Bad{why}:
      IO.die(Unit, 1, "ez: error: " ++ why)
    case M.Good{m}:
      go.good(m, src, lib, dir, rev, act)

# the checkout's ledger, built into `dir`. `Run` starts the binary.
def go(+src: String, +lib: String, +dir: String, +rev: String,
  act: Act) -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load(src)
    go.read(r, src, lib, dir, rev, act)

# a checkout replaced with this commit. The rev file is left alone until the
# build has written a binary for it.
def clone(+src: String, +url: String, +rev: String) -> IO(Unit):
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", src])
    Git.clone(src, url, rev)

# clone when the checkout is not already this commit
def sync(need: Bool, +src: String, +url: String, +rev: String) -> IO(Unit):
  match need:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      clone(src, url, rev)

# the checkout and the binary for one remote, once the cache root and the
# commit are known
def run.remote.at(+root: String, +url: String, +slug: String, +rev: String,
  act: Act) -> IO(Unit):
  +dir = root ++ "/" ++ slug
  +src = dir ++ "/src"
  do IO<Unit>:
    +cached : String <- text(dir ++ "/rev")
    +src_ok : Bool <- is.file(src ++ "/ez.toml")
    sync(Bool.not(fresh(src_ok, cached, rev)), src, url, rev)
    go(src, src ++ "/.ez/lib", dir, rev, act)

# a remote: the cache holds the checkout and the binary
def run.remote(+url: String, +slug: String, act: Act) -> IO(Unit):
  do IO<Unit>:
    +root : String <- cache.root()
    +rev : String <- head.ask(url)
    run.remote.at(root, url, slug, rev, act)

# a path, once it is absolute and its commit is known
def run.local.at(+root: String, +abs: String, +rev: String, act: Act) -> IO(Unit):
  +dir = root ++ "/local" ++ abs
  go(abs, dir ++ "/lib", dir, rev, act)

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
def run.go(p: Tgt.Place, act: Act) -> IO(Unit):
  match p:
    case Tgt.Bad{why}:
      run.bad(why)
    case Tgt.Local{path}:
      run.local(path, act)
    case Tgt.Remote{url, slug}:
      run.remote(url, slug, act)

# `ez tool run <target> [-- args…]`, and what `ezx` runs
def run(+target: String, args: List<&2, String>) -> IO(Unit):
  run.go(Tgt.classify(target), Run{args})

# `ez tool install <target>`: the lock fetched, the binary built, not run
def install(+target: String) -> IO(Unit):
  run.go(Tgt.classify(target), Hold{})

# `ez tool upgrade <target>`: the same resolution `run` uses, and a rebuild
# when that commit is not the one on record. The binary is not run.
def upgrade(+target: String) -> IO(Unit):
  run.go(Tgt.classify(target), Hold{})

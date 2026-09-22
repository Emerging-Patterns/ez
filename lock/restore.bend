# lock/restore: BEND_LIB filled from the lock alone, so a checkout builds
# without re-resolving anything. This is what nix/bend-lib.nix does inside a
# sandbox, done here for people who are not building through nix.
import Base
import ../io/file.bend as F
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../sha/sha.bend as Sha
import ../hub/hub.bend as Web
import ../git/git.bend as Git
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../pkg/pkg.bend as K
import ../pkg/path.bend as P
import ./lock.bend as L
import ../ez/say.bend as Say

# a write that did not happen is a failure, not a silence
def wrote(ok: Bool, at: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " could not be written")

# one file of a package, put where bend will look for it
def put(+lib: String, +hash: String, at: String, text: String) -> IO(Unit):
  +dst = lib ++ "/" ++ hash ++ "/" ++ at
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", P.dir(dst)])
    ok : Bool <- F.write(dst, text)
    wrote(ok, dst)

# one file of a hub package, fetched and checked against the lock
def hub.one(+hub: String, +lib: String, +hash: String, +f: K.File) -> IO(Unit):
  do IO<Unit>:
    g : Web.Got <- Web.fetch(L.url_of(hub, hash, K.file.at(f)), K.file.sum(f))
    text : String <- L.body_of(g)
    put(lib, hash, K.file.at(f), text)

# every file of a hub package
def hub.all(+hub: String, +lib: String, +hash: String, fs: List<&2, K.File>) -> IO(Unit):
  match fs:
    case []:
      IO.pure(Unit, Unit{})
    case h <> t:
      do IO<Unit>:
        hub.one(hub, lib, hash, h)
        hub.all(hub, lib, hash, t)

# a file of a checkout that does not hash to what the lock says is not the file
# the lock meant
def git.judge(ok: Bool, at: String, lib: String, hash: String, to: String,
  text: String) -> IO(Unit):
  match ok:
    case True{}:
      put(lib, hash, to, text)
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " does not match the lock")

# one file of a checkout, checked and put in place
def git.one(+from: String, +lib: String, +hash: String, +f: K.File) -> IO(Unit):
  +at = P.join(from, K.file.at(f))
  do IO<Unit>:
    m : Maybe<&2, String> <- F.read(at)
    +text : String <- IO.pure(String, F.text_of(m))
    git.judge(String.eq(Sha.hex(text), K.file.sum(f)), at, lib, hash,
      K.file.at(f), text)

# every file of a checkout
def git.all(+from: String, +lib: String, +hash: String, fs: List<&2, K.File>) -> IO(Unit):
  match fs:
    case []:
      IO.pure(Unit, Unit{})
    case h <> t:
      do IO<Unit>:
        git.one(from, lib, hash, h)
        git.all(from, lib, hash, t)

# a vendored package, rebuilt from the rev the lock pins. Its paths are written
# from the package's root inside the repo, which is not always the entry's own
# directory. The line names the package and the repo before the fetch starts.
def git.pkg(+lib: String, +hash: String, +url: String, rev: String, +entry: String,
  root: String, fs: List<&2, K.File>) -> IO(Unit):
  +work = lib ++ "/.work-" ++ hash
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", work])
    Git.clone.say(work, url, rev, Say.dep.git(Say.label(hash, entry), url))
    git.all(P.join(work, root), lib, hash, fs)
    _cl : String <- R.exec(["rm", "-rf", work])
    return Unit{}

# a hub package, fetched and said so before the first byte
def source.hub(+hub: String, +lib: String, +hash: String, fs: List<&2, K.File>) -> IO(Unit):
  do IO<Unit>:
    +s : Say.Spin <- Say.hold(Say.dep.hub(hash))
    hub.all(hub, lib, hash, fs)
    Say.done(s)

# a package, from wherever the lock says it comes from
def source(hub: String, +lib: String, +hash: String, src: L.Src,
  fs: List<&2, K.File>) -> IO(Unit):
  match src:
    case L.Hub{}:
      source.hub(hub, lib, hash, fs)
    case L.Git{url, rev, entry, root, _nar, _tag}:
      git.pkg(lib, hash, url, rev, entry, root, fs)

# the name a line uses: the entry's, or the hash when the package has no entry
def pkg.label(+hash: String, src: L.Src) -> String:
  match src:
    case L.Hub{}:
      hash
    case L.Git{_url, _rev, entry, _root, _nar, _tag}:
      Say.label(hash, entry)

# the package laid out. The manifest is written last, so a tree that has it
# is a tree that finished.
def one.live(hub: String, +lib: String, +p: L.Pack) -> IO(Unit):
  +hash = L.pack.hash(p)
  do IO<Unit>:
    _rm : String <- R.exec(["rm", "-rf", lib ++ "/" ++ hash])
    source(hub, lib, hash, L.pack.src(p), L.pack.files(p))
    put(lib, hash, "manifest", L.pack.manifest(p))

# a tree whose manifest is already the one the lock would write
def one.pick(hit: Bool, hub: String, +lib: String, +p: L.Pack) -> IO(Unit):
  match hit:
    case True{}:
      IO.print_err(Say.dep.cached(pkg.label(L.pack.hash(p), L.pack.src(p))))
    case False{}:
      one.live(hub, lib, p)

def one.seen(m: Maybe<&2, String>, +man: String, hub: String, +lib: String,
  +p: L.Pack) -> IO(Unit):
  match m:
    case None{}:
      one.live(hub, lib, p)
    case Some{text}:
      one.pick(String.eq(text, man), hub, lib, p)

# one package of the lock, laid out the way the hub serves it: the files, and
# the manifest beside them. A manifest already on disk is the package.
def one(hub: String, +lib: String, +p: L.Pack) -> IO(Unit):
  +hash = L.pack.hash(p)
  +man = L.pack.manifest(p)
  do IO<Unit>:
    m : Maybe<&2, String> <- F.read(lib ++ "/" ++ hash ++ "/manifest")
    one.seen(m, man, hub, lib, p)

# every package of the lock
def all(+hub: String, +lib: String, ps: List<&2, L.Pack>) -> IO(Unit):
  match ps:
    case []:
      IO.pure(Unit, Unit{})
    case h <> t:
      do IO<Unit>:
        one(hub, lib, h)
        all(hub, lib, t)

# the lock read, and BEND_LIB filled from it
def restore.at(+ss: List<&2, T.Sect>, lib: String) -> IO(Unit):
  all(L.lock.hub(ss), lib, L.packs(ss))

# BEND_LIB filled from a lock file
def restore(at: String) -> IO(Unit):
  do IO<Unit>:
    lib : String <- L.lib()
    m : Maybe<&2, String> <- F.read(at)
    restore.at(T.sects(T.parse(F.text_of(m))), lib)

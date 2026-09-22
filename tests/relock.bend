# `ez lock` from the ledger alone: what a fresh clone can do. `ez add` writes
# two records of where a package came from, one in ez.toml and one in
# .ez/origins.toml, and lays the package's tree under .ez/lib; .gitignore
# keeps the second record and the tree out of the repo. So a clone has the
# ledger and neither of the others, and the lock it writes has to be the lock
# that was committed. This test takes the cache and the tree away and asks
# again: the lock fetches the tree at the ledger's rev and checks it.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../ez/quiet.bend as Q
import ../check/kit.bend as Check
import ../check/world.bend as W

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# the upstream package: a repo with one file, committed and never published
def upstream(+at: String) -> IO(String):
  do IO<String>:
    W.mkdir(at ++ "/src")
    _w : Bool <- F.write(at ++ "/src/lib.bend",
      "import Base\n\n# double the number\ndef double(+x: U32) -> U32:\n" ++
      "  (x * 2 : U32)\n")
    _i : String <- R.exec(["git", "-C", at, "init", "-q"])
    _a : String <- R.exec(["git", "-C", at, "add", "-A"])
    _c : String <- R.exec(["git", "-C", at, "-c", "user.email=t@t",
      "-c", "user.name=t", "commit", "-q", "-m", "init"])
    _p : String <- R.exec(["git", "-C", at, "config",
      "uploadpack.allowAnySHA1InWant", "true"])
    +rev : String <- R.exec(["git", "-C", at, "rev-parse", "HEAD"])
    return W.line(rev)

# a project that depends on that repo, locked once with everything in place
def built(+repo: String, +app: String, +url: String, +rev: String) -> IO(String):
  do IO<String>:
    _i : String <- R.exec(W.ez(repo, app, ["init", "myapp", "main.bend"]))
    +out : String <- R.exec(W.ez(repo, app, ["add", url, rev, "src/lib.bend"]))
    yes("add vendors a package from a repo", R.ok(out))
    +t : Maybe<&2, String> <- F.read(app ++ "/ez.toml")
    +hash : String <- IO.pure(String, W.value(F.text_of(t), "hash"))
    _w : Bool <- F.write(app ++ "/main.bend",
      "import Base\nimport " ++ hash ++ "/lib.bend as L\n\n" ++
      "def main() -> U32:\n  L.double(21)\n")
    W.track(app)
    +l : String <- R.exec(W.ez(repo, app, ["lock"]))
    yes("lock writes a lock with the cache in place", R.ok(l))
    return hash

# the same project with the gitignored cache and tree gone, which is the state
# of a clone. `ez add` is not run again: the committed ledger is all there is.
def again(+repo: String, +app: String, +was: String) -> IO(Unit):
  do IO<Unit>:
    W.rm(app ++ "/.ez/origins.toml")
    W.rm(app ++ "/.ez/lib")
    +gone : String <- R.exec(["test", "-e", app ++ "/.ez/origins.toml"])
    yes("the cache is gone", Bool.not(R.ok(gone)))
    +l : String <- R.exec(W.ez(repo, app, ["lock"]))
    yes("lock succeeds from the ledger alone", R.ok(l))
    +now : Maybe<&2, String> <- F.read(app ++ "/ez.lock.toml")
    Check.eq_str("and writes the same lock, to the byte",
      Q.chomp(F.text_of(now)), Q.chomp(was))

# everything, once the scratch directory and the binary are known
def go(+repo: String, +root: String) -> IO(Unit):
  do IO<Unit>:
    +rev : String <- upstream(root ++ "/upstream")
    W.mkdir(root ++ "/app")
    _h : String <- built(repo, root ++ "/app", root ++ "/upstream", rev)
    +was : Maybe<&2, String> <- F.read(root ++ "/app/ez.lock.toml")
    again(repo, root ++ "/app", F.text_of(was))
    W.rm(root)

def main() -> IO(Unit):
  do IO<Unit>:
    repo : String <- W.here()
    root : String <- W.tmp()
    go(repo, root)

#|ok add vendors a package from a repo
#|ok lock writes a lock with the cache in place
#|ok the cache is gone
#|ok lock succeeds from the ledger alone
#|ok and writes the same lock, to the byte

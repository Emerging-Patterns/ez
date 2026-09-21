# lock: BEND_LIB filled from a lock alone. The package here is a vendored one,
# rebuilt from a git repo the test makes and serves over file://, so nothing
# reaches the network.
import Base
import ../lock.bend as L
import ../restore.bend as Restore
import ../../io/file.bend as F
import ../../run/run.bend as R
import ../../sha/sha.bend as Sha
import ../../pkg/pkg.bend as K
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../../check/kit.bend as Check

# the package name the fixture uses
def hash() -> String:
  "0xdddddddddddddddddddddddddddddddd"

# the one file of the package
def leaf() -> String:
  "import Base\n\n# double the number\ndef double(+x: U32) -> U32:\n  (x * 2 : U32)\n"

# a repo holding the package under src/, committed, and willing to serve the
# commit by name
def repo(+d: String) -> IO(String):
  do IO<String>:
    _mk : String <- R.exec(["mkdir", "-p", d ++ "/repo/src"])
    _w : Bool <- F.write(d ++ "/repo/src/lib.bend", leaf())
    _i : String <- R.exec(["git", "init", "-q", d ++ "/repo"])
    _a : String <- R.exec(["git", "-C", d ++ "/repo", "add", "-A"])
    _c : String <- R.exec(["git", "-C", d ++ "/repo", "-c", "user.email=t@t",
      "-c", "user.name=t", "commit", "-q", "-m", "init"])
    _s : String <- R.exec(["git", "-C", d ++ "/repo", "config",
      "uploadpack.allowAnySHA1InWant", "true"])
    +out : String <- R.exec(["git", "-C", d ++ "/repo", "rev-parse", "HEAD"])
    return String.trim(R.text(out))

# the lock that package would be written into: pinned to the commit, with its
# paths written from src/ inside the repo
def lock(+d: String, rev: String) -> String:
  L.render("https://hub.example", "2.0.16",
    [L.Pack{hash(), L.Git{"file://" ++ d ++ "/repo", rev, "src/lib.bend", "src",
      "sha256-zz", ""}, [K.File{"lib.bend", Sha.hex(leaf())}]}])

# what landed at a path
def landed(m: Maybe<&2, String>) -> String:
  F.text_of(m)

def main() -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(["mktemp", "-d"])
    +d : String <- IO.pure(String, String.trim(R.text(out)))
    rev : String <- repo(d)
    Restore.restore.at(T.sects(T.parse(lock(d, rev))), d ++ "/lib")
    f : Maybe<&2, String> <- F.read(d ++ "/lib/" ++ hash() ++ "/lib.bend")
    Check.eq_str("the package's file is rebuilt from the rev", landed(f), leaf())
    m : Maybe<&2, String> <- F.read(d ++ "/lib/" ++ hash() ++ "/manifest")
    Check.eq_str("the manifest is written beside it", landed(m),
      Sha.hex(leaf()) ++ " lib.bend\n")
    _rm : String <- R.exec(["rm", "-rf", d])
    return Unit{}

#|0xdddddddddddddddddddddddddddddddd git
#|ok the package's file is rebuilt from the rev
#|ok the manifest is written beside it

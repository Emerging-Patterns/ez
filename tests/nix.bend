# The nix path, end to end: a project locked against a hub, then built by
# `nix-build`, where the sandbox reaches that hub only through the lock's own
# fixed-output fetches. This is the gap ez exists to close — bend resolves a
# hub import during the check, inside `book_load`, and a nix build cannot.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../sha/sha.bend as Sha
import ../ez/quiet.bend as Q
import ../check/kit.bend as Check
import ../check/world.bend as W

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# what a program answered, with bend's check report taken out of it
def answer(+out: String) -> String:
  W.last(String.lines(Q.filter(R.text(out))))

# a one-file package written into a hub directory, under the name its own
# manifest's digest gives it
def publish(+hub: String, +at: String, +text: String) -> IO(String):
  do IO<String>:
    +man : String <- IO.pure(String, Sha.hex(text) ++ " " ++ at ++ "\n")
    +h : String <- IO.pure(String, "0x" ++ String.take(Sha.hex(man), 32n))
    W.mkdir(hub ++ "/" ++ h ++ "/src")
    _f : Bool <- F.write(hub ++ "/" ++ h ++ "/" ++ at, text)
    _m : Bool <- F.write(hub ++ "/" ++ h ++ "/manifest", man)
    return h

# the lock nix reads, written from the entry against the hub that is up, which
# is the hub the ledger names
def lock(+repo: String, +app: String, +hub: String) -> IO(String):
  do IO<String>:
    _t : Bool <- F.write(app ++ "/ez.toml",
      "[package]\nname = \"app\"\nhub = \"" ++ hub ++ "\"\n")
    W.track(app)
    _o : String <- R.exec(W.ez(repo, app, ["lock"]))
    +at : String <- W.only(app, "ez.lock.*")
    yes("the lock was written", Bool.not(String.is_empty(at)))
    return at

# the BEND_LIB nix builds out of that lock, and the build that then needs no
# hub at all
def sandbox(+repo: String, +app: String, +hash: String, +lock: String) -> IO(Unit):
  do IO<Unit>:
    _n : Bool <- F.write(app ++ "/build.nix",
      "let pkgs = import <nixpkgs> { };\nin pkgs.callPackage " ++ repo ++
      "/nix/bend-lib.nix { } " ++ lock ++ "\n")
    +out : String <- R.exec(["nix-build", "--no-out-link", app ++ "/build.nix"])
    +at : String <- IO.pure(String,
      W.starting.last(String.lines(R.text(out)), "/nix/store/", ""))
    +got : String <- R.exec(["test", "-f", at ++ "/" ++ hash ++ "/src/lib.bend"])
    yes("nix fetched the package through the lock", R.ok(got))
    +ran : String <- R.exec(W.inside(app, ["env", "BEND_HUB=http://127.0.0.1:1",
      "BEND_LIB=" ++ at, "bend", "main.bend"]))
    Check.eq_str("the store path builds with the hub unreachable",
      answer(ran), "42")

# everything, once the scratch directory and the port are known
def go(+repo: String, +root: String, +port: String) -> IO(Unit):
  do IO<Unit>:
    W.mkdir(root ++ "/app")
    +a : String <- publish(root ++ "/hub", "src/lib.bend",
      "import Base\n\n# double the number\ndef double(+x: U32) -> U32:\n" ++
      "  (x * 2 : U32)\n")
    _w : Bool <- F.write(root ++ "/app/main.bend",
      "import Base\nimport " ++ a ++ "/src/lib.bend as A\n\n" ++
      "def main() -> U32:\n  A.double(21)\n")
    +pid : String <- W.spawn(W.inside(root ++ "/hub", ["python3", "-m",
      "http.server", port, "--bind", "127.0.0.1"]))
    up : Bool <- W.ready(["curl", "-fsS", "--max-time", "5",
      "http://127.0.0.1:" ++ port ++ "/"])
    yes("the hub answers", up)
    +at : String <- lock(repo, root ++ "/app", "http://127.0.0.1:" ++ port)
    sandbox(repo, root ++ "/app", a, at)
    W.stop(pid)
    W.rm(root)

def main() -> IO(Unit):
  do IO<Unit>:
    repo : String <- W.here()
    root : String <- W.tmp()
    port : String <- W.port()
    go(repo, root, port)

#|ok the hub answers
#|ok the lock was written
#|ok nix fetched the package through the lock
#|ok the store path builds with the hub unreachable

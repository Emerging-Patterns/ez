# A hub two levels deep — package B imports package A — locked from an entry
# that imports B, and then built with the hub unreachable. That last step is
# the whole point of ez: bend resolves a hub import during the check, and a nix
# sandbox has no network to do it with.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ../sha/sha.bend as Sha
import ../ez/drift.bend as D
import ../ez/quiet.bend as Q
import ../check/kit.bend as Check
import ../check/world.bend as W

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# what a program answered, with bend's check report taken out of it
def answer(+out: String) -> String:
  W.last(String.lines(Q.filter(R.text(out))))

# a package's manifest: one `<sha256> <path>` line per file, in path order.
# Every package here holds one file, which is all this test needs.
def manifest(+text: String, +at: String) -> String:
  Sha.hex(text) ++ " " ++ at ++ "\n"

# the name a package takes, which is the first 32 hex characters of its
# manifest's own digest, the way `bend --publish` computes it
def name(+man: String) -> String:
  "0x" ++ String.take(Sha.hex(man), 32n)

# a package written into the hub directory, and the name it took
def publish(+hub: String, +at: String, +text: String) -> IO(String):
  do IO<String>:
    +man : String <- IO.pure(String, manifest(text, at))
    +h : String <- IO.pure(String, name(man))
    W.mkdir(hub ++ "/" ++ h ++ "/src")
    _f : Bool <- F.write(hub ++ "/" ++ h ++ "/" ++ at, text)
    _m : Bool <- F.write(hub ++ "/" ++ h ++ "/manifest", man)
    return h

# every package hash the lock names, sorted and said once each. The lock is
# grepped rather than parsed, so its format is not this test's business.
def named(+at: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- R.exec(["grep", "-ohE", "0x[0-9a-f]{32}", at])
    return D.uniq(List.sort(~String, ~String.is_le,
      W.nonblank(String.lines(R.text(out)))))

# the entry, locked against the hub that is serving the two packages
def lock(+repo: String, +app: String, +hub: String) -> IO(Unit):
  do IO<Unit>:
    _o : String <- R.exec(W.inside(app, ["env", "BEND_HUB=" ++ hub,
      "EZ_ROOT=" ++ repo, repo ++ "/bin/ez.bin", "lock"]))
    return Unit{}

# BEND_LIB filled from the lock and nothing else, which is what the nix
# derivation does and what a checkout without a network needs
def restore(+repo: String, +app: String, +hub: String) -> IO(Unit):
  do IO<Unit>:
    _o : String <- R.exec(W.inside(app, ["env", "BEND_HUB=" ++ hub,
      "EZ_ROOT=" ++ repo, repo ++ "/bin/ez.bin", "fetch"]))
    return Unit{}

# the entry built against a BEND_LIB, with the hub pointed at a dead port so a
# fallback to the network cannot be what made it work
def build(+app: String, +lib: String) -> IO(String):
  R.exec(W.inside(app, ["env", "BEND_HUB=http://127.0.0.1:1",
    "BEND_LIB=" ++ lib, "bend", "main.bend"]))

# everything, once the scratch directory and the port are known
def go(+repo: String, +root: String, +port: String) -> IO(Unit):
  do IO<Unit>:
    W.mkdir(root ++ "/app")
    W.mkdir(root ++ "/empty")
    +a : String <- publish(root ++ "/hub", "src/lib.bend",
      "import Base\n\n# double the number\ndef double(+x: U32) -> U32:\n" ++
      "  (x * 2 : U32)\n")
    +b : String <- publish(root ++ "/hub", "src/mid.bend",
      "import Base\nimport " ++ a ++ "/src/lib.bend as A\n\n" ++
      "# four times the number\ndef quad(+x: U32) -> U32:\n" ++
      "  A.double(A.double(x))\n")
    _w : Bool <- F.write(root ++ "/app/main.bend",
      "import Base\nimport " ++ b ++ "/src/mid.bend as B\n\n" ++
      "def main() -> U32:\n  B.quad(11)\n")
    +pid : String <- W.spawn(W.inside(root ++ "/hub", ["python3", "-m",
      "http.server", port, "--bind", "127.0.0.1"]))
    up : Bool <- W.ready(["curl", "-fsS", "--max-time", "5",
      "http://127.0.0.1:" ++ port ++ "/"])
    yes("the hub answers", up)
    lock(repo, root ++ "/app", "http://127.0.0.1:" ++ port)
    +at : String <- W.only(root ++ "/app", "ez.lock.*")
    yes("the lock was written", Bool.not(String.is_empty(at)))
    hs : List<&2, String> <- named(at)
    Check.eq_str("the lock names both packages, the direct one and its own " ++
      "dependency", String.join(hs, "\n"),
      String.join(List.sort(~String, ~String.is_le, [a, b]), "\n"))
    restore(repo, root ++ "/app", "http://127.0.0.1:" ++ port)
    W.stop(pid)
    +good : String <- build(root ++ "/app", root ++ "/app/.ez/lib")
    Check.eq_str("the locked lib builds with the hub unreachable",
      answer(good), "44")
    +bad : String <- build(root ++ "/app", root ++ "/empty")
    yes("without the locked lib the same build fails", Bool.not(R.ok(bad)))
    W.rm(root)

def main() -> IO(Unit):
  do IO<Unit>:
    repo : String <- W.here()
    root : String <- W.tmp()
    port : String <- W.port()
    go(repo, root, port)

#|ok the hub answers
#|ok the lock was written
#|ok the lock names both packages, the direct one and its own dependency
#|ok the locked lib builds with the hub unreachable
#|ok without the locked lib the same build fails

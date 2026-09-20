# `ez` driven through a whole project: a ledger written, a git package that was
# never published added to it, locked, fetched into a BEND_LIB of its own,
# checked, run, tested, and removed again. The remote is taken away before the
# check, so nothing here can quietly be falling back to the network.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ../ez/quiet.bend as Q
import ../check/kit.bend as Check
import ../check/world.bend as W

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# a line kept or dropped
def put(keep: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match keep:
    case True{}:
      h <> rest
    case False{}:
      rest

# the lines from the one that starts with this on. `on` turns true at that
# line and stays true, so the decision is made once per line and the walk
# needs no second pass.
def since(ls: List<&2, String>, +pre: String, on: Bool) -> List<&2, String>:
  match ls:
    case []:
      []
    case +h <> t:
      +keep = Bool.or(on, String.starts_with(h, pre))
      put(keep, h, since(t, pre, keep))

# a stanza of a ledger, from its heading to the end of the file
def stanza(+text: String, +head: String) -> String:
  Q.chomp(String.join(since(String.lines(text), head, False{}), "\n"))

# `ez` run in a project directory. EZ_ROOT is how the binary finds the
# TypeScript it has not absorbed yet, since IO.args() carries no argv[0].
def ez(+repo: String, +app: String, args: List<&2, String>) -> List<&2, String>:
  W.inside(app, List.append(&2, String,
    ["env", "EZ_ROOT=" ++ repo, repo ++ "/bin/ez.bin"], args))

# what a program answered, with bend's check report taken out of it, since a
# run's output and the check that preceded it arrive on the same stream
def answer(+out: String) -> String:
  W.last(String.lines(Q.filter(R.text(out))))

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
    +rev : String <- R.exec(["git", "-C", at, "rev-parse", "HEAD"])
    return W.line(rev)

# that repo served the way a real remote is, so `ez add` reaches it over the
# protocol and not over the file system
def serve(+at: String, +port: String) -> IO(String):
  do IO<String>:
    W.mkdir(at ++ "/srv")
    _c : String <- R.exec(["git", "clone", "-q", "--bare", at ++ "/upstream",
      at ++ "/srv/upstream.git"])
    _f : String <- R.exec(["git", "-C", at ++ "/srv/upstream.git", "config",
      "uploadpack.allowAnySHA1InWant", "true"])
    pid : String <- W.spawn(["git", "daemon", "--reuseaddr",
      "--listen=127.0.0.1", "--port=" ++ port, "--base-path=" ++ at ++ "/srv",
      "--export-all"])
    up : Bool <- W.ready(["git", "ls-remote",
      "git://127.0.0.1:" ++ port ++ "/upstream.git"])
    yes("the upstream remote answers", up)
    return pid

# the ledger, the lock and the vendored tree, each asked what it holds
def ledger(+repo: String, +app: String, +url: String, +rev: String) -> IO(String):
  do IO<String>:
    _i : String <- R.exec(ez(repo, app, ["init", "myapp", "main.bend"]))
    t : Maybe<&2, String> <- F.read(app ++ "/ez.toml")
    Check.eq_str("init writes a ledger", Q.chomp(F.text_of(t)),
      "[package]\nname = \"myapp\"\nentry = \"main.bend\"")
    _a : String <- R.exec(ez(repo, app, ["add", url, rev, "src/lib.bend"]))
    +t2 : Maybe<&2, String> <- F.read(app ++ "/ez.toml")
    +hash : String <- IO.pure(String, W.value(F.text_of(t2), "hash"))
    Check.eq_str("add records the package under its name",
      stanza(F.text_of(t2), "[deps.lib]"),
      "[deps.lib]\nhash = \"" ++ hash ++ "\"\ngit = \"" ++ url ++
      "\"\nrev = \"" ++ rev ++ "\"\nentry = \"src/lib.bend\"")
    return hash

# the project that depends on it, and every question `ez` answers about it once
# the remote it came from is gone
def project(+repo: String, +app: String, +hash: String, +rev: String) -> IO(Unit):
  do IO<Unit>:
    _w : Bool <- F.write(app ++ "/main.bend",
      "import Base\nimport " ++ hash ++ "/lib.bend as L\n\n" ++
      "def main() -> U32:\n  L.double(21)\n")
    _l : String <- R.exec(ez(repo, app, ["lock"]))
    +lock : Maybe<&2, String> <- F.read(app ++ "/ez.lock.json")
    yes("lock records the git source",
      Bool.and(String.contains(F.text_of(lock), "git"),
        String.contains(F.text_of(lock), rev)))
    W.rm(app ++ "/.ez/lib")
    _f : String <- R.exec(ez(repo, app, ["fetch"]))
    +got : String <- R.exec(["test", "-f",
      app ++ "/.ez/lib/" ++ hash ++ "/lib.bend"])
    yes("fetch fills BEND_LIB from the lock alone", R.ok(got))

# what `ez` says once there is no remote left to ask
def offline(+repo: String, +app: String) -> IO(Unit):
  do IO<Unit>:
    +ck : String <- R.exec(ez(repo, app, ["check"]))
    yes("check passes with the git remote gone", R.ok(ck))
    +rn : String <- R.exec(ez(repo, app, ["run"]))
    Check.eq_str("run gives the program's answer", answer(rn), "42")

# the test runner, on a file that prints its trailer and then on one that does
# not, because a runner that cannot fail is not one
def runner(+repo: String, +app: String) -> IO(Unit):
  do IO<Unit>:
    W.mkdir(app ++ "/src/tests")
    _w : Bool <- F.write(app ++ "/src/tests/ok.bend",
      "import Base\n\ndef main() -> IO(Unit):\n  IO.print(\"ok one\")\n\n#|ok one\n")
    +good : String <- R.exec(ez(repo, app, ["test", "--js-only"]))
    Check.eq_str("test passes a file that prints its trailer", answer(good),
      "PASS: 1 / 1")
    _b : Bool <- F.write(app ++ "/src/tests/bad.bend",
      "import Base\n\ndef main() -> IO(Unit):\n  IO.print(\"ok one\")\n\n#|ok two\n")
    +bad : String <- R.exec(ez(repo, app, ["test", "--js-only"]))
    yes("test fails a file that does not", Bool.not(R.ok(bad)))
    W.rm(app ++ "/src/tests/bad.bend")

# the ledger and the source disagreeing, which is the finding ez exists for:
# the package is dropped from the ledger while the import line stays
def drifted(+repo: String, +app: String, +hash: String) -> IO(Unit):
  do IO<Unit>:
    +ok : String <- R.exec(ez(repo, app, ["doctor"]))
    yes("doctor passes a project with nothing wrong", R.ok(ok))
    _r : String <- R.exec(ez(repo, app, ["remove", "lib"]))
    +t : Maybe<&2, String> <- F.read(app ++ "/ez.toml")
    yes("remove drops it from the ledger",
      Bool.not(String.contains(F.text_of(t), "deps.lib")))
    Check.eq_str("and leaves the package stanza alone",
      W.value(F.text_of(t), "name"), "myapp")
    +bad : String <- R.exec(ez(repo, app, ["doctor"]))
    yes("doctor reports a hash the ledger no longer names",
      String.contains(R.text(bad), "drift: " ++ hash ++ " is imported"))
    yes("and that drift fails the command", Bool.not(R.ok(bad)))
    +no : String <- R.exec(ez(repo, app, ["nonsense"]))
    yes("an unknown subcommand fails", Bool.not(R.ok(no)))

# everything, once the scratch directory, the port and the binary are known
def go(+repo: String, +root: String, +port: String) -> IO(Unit):
  do IO<Unit>:
    +rev : String <- upstream(root ++ "/upstream")
    +pid : String <- serve(root, port)
    W.mkdir(root ++ "/app")
    +hash : String <- ledger(repo, root ++ "/app",
      "git://127.0.0.1:" ++ port ++ "/upstream.git", rev)
    project(repo, root ++ "/app", hash, rev)
    W.stop(pid)
    offline(repo, root ++ "/app")
    runner(repo, root ++ "/app")
    drifted(repo, root ++ "/app", hash)
    W.rm(root)

def main() -> IO(Unit):
  do IO<Unit>:
    repo : String <- W.here()
    root : String <- W.tmp()
    port : String <- W.port()
    go(repo, root, port)

#|ok the upstream remote answers
#|ok init writes a ledger
#|ok add records the package under its name
#|ok lock records the git source
#|ok fetch fills BEND_LIB from the lock alone
#|ok check passes with the git remote gone
#|ok run gives the program's answer
#|ok test passes a file that prints its trailer
#|ok test fails a file that does not
#|ok doctor passes a project with nothing wrong
#|ok remove drops it from the ledger
#|ok and leaves the package stanza alone
#|ok doctor reports a hash the ledger no longer names
#|ok and that drift fails the command
#|ok an unknown subcommand fails

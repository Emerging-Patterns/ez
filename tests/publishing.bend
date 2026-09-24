# `ez publish`, driven end to end against a real hub. `tests/publish.bend`
# pins the hash ez computes against the one a real `bend --publish` mines;
# this drives the command that does it, and the three ways it is supposed to
# stop.
#
# The hub is check/oracle.bend, never the real one, and every run here names it
# explicitly. The two runs that must fail either never reach a hub at all,
# since a dirty tree is refused before anything is sent, or reach
# check/liar.bend, a `bend` that uploads nothing.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../ez/quiet.bend as Q
import ../pub/plan.bend as P
import ../check/kit.bend as Check
import ../check/world.bend as W

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# what a program printed, with bend's check report and the trailing blank gone
def said(+out: String) -> List<&2, String>:
  String.lines(Q.filter(R.text(out)))

# an environment variable's text; unset, ""
def text_of(res: Result<&1, &1, U32 & String, String>) -> String:
  match res:
    case Fail{_e}:
      ""
    case Done{s}:
      s

# the PATH this test is running under, so a run can be given one with a `bend`
# of its own in front of it and the real git and coreutils still behind
def path() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("PATH")
    return text_of(r)

# `ez` run in the project with these variables set for it. `env` takes the
# assignments before the command, and `W.inside` has already put an `env`
# there.
def ez(+repo: String, +app: String, vars: List<&2, String>, args: List<&2, String>) -> List<&2, String>:
  W.inside(app, List.append(&2, String, vars,
    List.append(&2, String, [repo ++ "/bin/ez.bin"], args)))

# the project being published: the nested layout `tests/publish.bend` uses, so
# that what goes to the hub is a package with an import across it and not a
# single file
def project(+app: String) -> IO(Unit):
  do IO<Unit>:
    W.mkdir(app ++ "/src/util")
    _m : Bool <- F.write(app ++ "/src/util/math.bend",
      "import Base\n\n# double the number\ndef double(+x: U32) -> U32:\n" ++
      "  (x * 2 : U32)\n")
    _l : Bool <- F.write(app ++ "/src/lib.bend",
      "import Base\nimport ./util/math.bend as M\n\n" ++
      "# four times the number\ndef quad(+x: U32) -> U32:\n" ++
      "  M.double(M.double(x))\n")
    return Unit{}

# the project's files committed, which is the state publishing insists on
def commit(+app: String) -> IO(Unit):
  do IO<Unit>:
    _a : String <- R.exec(["git", "-C", app, "add", "-A"])
    _c : String <- R.exec(["git", "-C", app, "-c", "user.email=t@t",
      "-c", "user.name=t", "commit", "-q", "-m", "init"])
    return Unit{}

# a tree with the project's files staged and nothing committed: `ez publish`
# must stop here, and must stop before it has spoken to anything. The hub is
# named all the same, so that a run which did reach it would have reached the
# oracle and not the real one.
def refuses.dirty(+repo: String, +app: String, +hub: String) -> IO(Unit):
  do IO<Unit>:
    _i : String <- R.exec(["git", "-C", app, "init", "-q"])
    _a : String <- R.exec(["git", "-C", app, "add", "-A"])
    +out : String <- R.exec(ez(repo, app, ["BEND_HUB=" ++ hub], ["publish"]))
    yes("publish stops on a dirty tree", Bool.not(R.ok(out)))
    yes("and says which file it was about",
      String.contains(R.text(out), "src/lib.bend"))
    yes("and reports no hash at all",
      Bool.not(String.contains(R.text(out), "import 0x")))
    yes("and says no hub description, since nothing was about to be sent",
      Bool.not(String.contains(R.text(out), "hub description")))

# the build output every project has and no project commits. `.ez/*` and
# `bin/<name>.out` are what `ez init` wrote into the project's .gitignore, so
# git never names them and a tree holding them is still clean.
def ignored(+app: String) -> IO(Unit):
  do IO<Unit>:
    _c : Bool <- F.write(app ++ "/.ez/check.js", "// build output\n")
    _b : Bool <- F.write(app ++ "/bin/myapp.out", "build output\n")
    return Unit{}

# the package fetched back out of the hub by the name publish reported, which
# is the question a consumer actually asks. A BEND_LIB of its own, so nothing
# the publishing project left on disk can answer for the hub.
def consumer(+root: String, +hub: String, +hash: String) -> IO(Unit):
  do IO<Unit>:
    W.mkdir(root ++ "/consumer/lib")
    _w : Bool <- F.write(root ++ "/consumer/main.bend",
      "import Base\nimport " ++ hash ++ "/lib.bend as Lib\n\n" ++
      "def main() -> U32:\n  Lib.quad(11)\n")
    +out : String <- R.exec(W.inside(root ++ "/consumer",
      ["env", "BEND_HUB=" ++ hub, "BEND_LIB=" ++ root ++ "/consumer/lib",
        "bend", "main.bend"]))
    Check.eq_str("a consumer's import of that name resolves and runs",
      W.last(said(out)), "44")

# the tree clean, the hub up, and the package sent. Two lines come back: the
# name ez computed, and the import line a consumer would write. Before the
# upload the line the hub will describe the package by goes to stderr: the
# package is `lib.bend` and `util/math.bend`, and `lib.bend` comes first.
def publishes(+repo: String, +app: String, +root: String, +hub: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(ez(repo, app, ["BEND_HUB=" ++ hub], ["publish"]))
    yes("publish sends from a tree whose only extra files are ignored",
      R.ok(out))
    +ls : List<&2, String> <- IO.pure(List<&2, String>, said(out))
    +hash : String <- IO.pure(String, W.nth(ls, 0n))
    yes("and reports a 0x name and nothing else on its first line",
      P.is_name(hash))
    Check.eq_str("and then the import line a consumer would write",
      W.nth(ls, 1n), "import " ++ hash ++ "/lib.bend as Lib")
    yes("and says, on stderr, the line the hub describes it by",
      String.contains(R.text(out), "hub description: import Base"))
    m : Maybe<&2, String> <- F.read(root ++ "/hub/" ++ hash ++ "/manifest")
    yes("the hub holds the package under the name publish reported",
      Bool.not(String.is_empty(F.text_of(m))))
    consumer(root, hub, hash)
    return hash

# an untracked file that no rule ignores. It is the case worth driving: the
# file set is read off the working tree, so a file no commit holds would be
# uploaded, and the import line would name a package nobody could rebuild.
def refuses.untracked(+repo: String, +app: String, +hub: String) -> IO(Unit):
  do IO<Unit>:
    _w : Bool <- F.write(app ++ "/notes.txt", "not committed\n")
    +out : String <- R.exec(ez(repo, app, ["BEND_HUB=" ++ hub], ["publish"]))
    yes("publish stops on an untracked file", Bool.not(R.ok(out)))
    yes("and names it", String.contains(R.text(out), "notes.txt"))
    _rm : String <- R.exec(["rm", "-f", app ++ "/notes.txt"])
    return Unit{}

# a `bend` whose package walk answers something else, built from
# check/liar.bend and put in front of the real one. This is the only way to
# make the two walks disagree, since they agree by construction, and it is the
# path the happy path can never catch.
def liar(+repo: String, +root: String) -> IO(String):
  do IO<String>:
    W.mkdir(root ++ "/bin")
    +out : String <- R.exec(["bend", repo ++ "/check/liar.bend", "-o",
      root ++ "/bin/bend"])
    yes("a bend that answers wrongly builds", R.ok(out))
    +p : String <- path()
    return "PATH=" ++ root ++ "/bin:" ++ p

# bend naming a different package. Neither number is reported as the package's
# name: the command exits non-zero, prints no import line, and says both so
# that the next question, which walk drifted, can be asked.
def refuses.differs(+repo: String, +app: String, +liar: String, +hash: String) -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(ez(repo, app, [liar], ["publish"]))
    yes("publish stops when bend names a different package",
      Bool.not(R.ok(out)))
    yes("and says both the hash it computed and the one bend printed",
      Bool.and(String.contains(R.text(out), hash),
        String.contains(R.text(out), "0xdeadbeefdeadbeefdeadbeefdeadbeef")))
    yes("and reports no import line for either of them",
      Bool.not(String.contains(R.text(out), "import 0x")))

# bend printing no line that is a name. Its output still holds one in the
# middle of two other lines, which is exactly what a loose pattern would find.
def refuses.unread(+repo: String, +app: String, +liar: String) -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(ez(repo, app, [liar, "EZ_LIAR=mute"], ["publish"]))
    yes("publish stops when bend's output names no package",
      Bool.not(R.ok(out)))
    yes("and says so rather than reaching for the one buried in another line",
      String.contains(R.text(out), "no line that is a 0x name"))

# everything, once the scratch directory and the port are known
def go(+repo: String, +root: String, +port: String) -> IO(Unit):
  +app = root ++ "/app"
  +hub = "http://127.0.0.1:" ++ port
  do IO<Unit>:
    project(app)
    _i : String <- R.exec(W.ez(repo, app, ["init", "myapp", "src/lib.bend"]))
    refuses.dirty(repo, app, hub)
    commit(app)
    ignored(app)
    W.mkdir(root ++ "/hub")
    +pid : String <- W.spawn(["env", "BEND_LIB=" ++ repo ++ "/.ez/lib",
      "bend", repo ++ "/check/oracle.bend", root ++ "/hub", port])
    up : Bool <- W.ready(["curl", "-fsS", "--max-time", "5", hub ++ "/"])
    yes("the oracle answers", up)
    +hash : String <- publishes(repo, app, root, hub)
    refuses.untracked(repo, app, hub)
    +lie : String <- liar(repo, root)
    refuses.differs(repo, app, lie, hash)
    refuses.unread(repo, app, lie)
    W.stop(pid)
    W.rm(root)

def main() -> IO(Unit):
  do IO<Unit>:
    repo : String <- W.here()
    root : String <- W.tmp()
    port : String <- W.port()
    go(repo, root, port)

#|ok publish stops on a dirty tree
#|ok and says which file it was about
#|ok and reports no hash at all
#|ok and says no hub description, since nothing was about to be sent
#|ok the oracle answers
#|ok publish sends from a tree whose only extra files are ignored
#|ok and reports a 0x name and nothing else on its first line
#|ok and then the import line a consumer would write
#|ok and says, on stderr, the line the hub describes it by
#|ok the hub holds the package under the name publish reported
#|ok a consumer's import of that name resolves and runs
#|ok publish stops on an untracked file
#|ok and names it
#|ok a bend that answers wrongly builds
#|ok publish stops when bend names a different package
#|ok and says both the hash it computed and the one bend printed
#|ok and reports no import line for either of them
#|ok publish stops when bend's output names no package
#|ok and says so rather than reaching for the one buried in another line

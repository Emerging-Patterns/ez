# check/world: the scratch world an end-to-end test builds around itself. These
# tests drive the real tools — git, curl, nix, a server on a port — so each one
# wants a directory of its own, a port nothing else is on, and a way to start
# something that outlives the call starting it. Base has no chdir, no mkdir and
# no sleep, so every one of those is a program: `env -C` runs a command in a
# directory, and `setsid --fork` returns as soon as the child is a session of
# its own. Nothing here goes through a shell.
import Base
import snap@1.4.0.0/main.bend as R
import ./out.bend as O

# the directory the test is running in, which is the repo `ez test` was run from
def here() -> IO(String):  # noqa: L001 IO: runs pwd
  do IO<String>:
    +out : String <- R.exec(["pwd"])
    return O.line(out)

# a fresh empty directory, removed when the test is done with it
def tmp() -> IO(String):  # noqa: L001 IO: runs mktemp
  do IO<String>:
    +out : String <- R.exec(["mktemp", "-d"])
    return O.line(out)

# a directory, and every directory above it
def mkdir(at: String) -> IO(Unit):  # noqa: L001 IO: runs mkdir
  do IO<Unit>:
    _o : String <- R.exec(["mkdir", "-p", at])
    return Unit{}

# a directory and everything under it, gone
def rm(at: String) -> IO(Unit):  # noqa: L001 IO: runs rm
  do IO<Unit>:
    _o : String <- R.exec(["rm", "-rf", at])
    return Unit{}

# a project's files, tracked by a repository of its own. `ez lock` starts from
# the `.bend` files git tracks, so a project a test writes is one it has to
# add before it locks; staged is enough, since `git ls-files` reads the index.
def track(+at: String) -> IO(Unit):  # noqa: L001 IO: runs git
  do IO<Unit>:
    _i : String <- R.exec(["git", "-C", at, "init", "-q"])
    _a : String <- R.exec(["git", "-C", at, "add", "-A"])
    return Unit{}

# the one file a pattern names, or "" when it names none. The lock's name is
# ez's business and not a test's, so a test looks for it rather than spelling
# it out.
def only(+at: String, +pat: String) -> IO(String):  # noqa: L001 IO: runs find
  do IO<String>:
    +out : String <- R.exec(["find", at, "-maxdepth", "1", "-name", pat])
    return O.first(O.nonblank(String.lines(R.text(out))))

# a TCP port nothing is listening on, so a stray server elsewhere can never
# answer for the one this test started
def port() -> IO(String):  # noqa: L001 IO: asks the host for a port
  do IO<String>:
    +out : String <- R.exec(["python3", "-c",
      "import socket; s=socket.socket(); s.bind((\"127.0.0.1\", 0)); " ++
      "print(s.getsockname()[1]); s.close()"])
    return O.line(out)

# a program started and left running, and the pid it was given. `R.exec` waits
# for what it runs and reads it to the end, which a server never reaches, so
# this is the other effect.
def spawn(args: List<&2, String>) -> IO(String):  # noqa: L001 IO: starts a program
  R.start(args)

# a started program stopped again, by the pid it was started with, so a test
# can never stop anything but what it started
def stop(pid: String) -> IO(Unit):  # noqa: L001 IO: runs kill
  do IO<Unit>:
    _o : String <- R.exec(["kill", pid])
    return Unit{}

# a command retried until it answers or the tries run out: how a test waits for
# the server it just started. A Bend server started on the interpreted lane
# takes tens of seconds to reach its first accept, so the count is generous. The verdict and the count are scrutinised
# together, so one def covers both endings and nothing recurses mutually.
def until(+args: List<&2, String>, tries: Nat, ok: Bool) -> IO(Bool):  # noqa: L001 IO: retries a program
  match tries ok:
    case _k True{}:
      IO.pure(Bool, True{})
    case 0n False{}:
      IO.pure(Bool, False{})
    case 1n+m False{}:
      do IO<Bool>:
        _s : String <- R.exec(["sleep", "0.1"])
        +out : String <- R.exec(args)
        until(args, m, R.ok(out))

# a server answered before the test went on without it
def ready(args: List<&2, String>) -> IO(Bool):  # noqa: L001 IO: waits on a program
  until(args, 600n, False{})

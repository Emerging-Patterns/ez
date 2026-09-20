# check/world: the scratch world an end-to-end test builds around itself. These
# tests drive the real tools — git, curl, nix, a server on a port — so each one
# wants a directory of its own, a port nothing else is on, and a way to start
# something that outlives the call starting it. Base has no chdir, no mkdir and
# no sleep, so every one of those is a program: `env -C` runs a command in a
# directory, and `setsid --fork` returns as soon as the child is a session of
# its own. Nothing here goes through a shell.
import Base
import ../run/run.bend as R

# the non-empty strings, which is what a program's output amounts to once its
# trailing newline has been counted as a line
def nonblank(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = nonblank(t)
      Bool.pick(List<&2, String>, String.is_empty(h), more, h <> more)

# the first line of a list of them
def first(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> t:
      h

# a one-line answer, without the newline the program ended it with
def line(+out: String) -> String:
  first(String.lines(R.text(out)))

# the last line of a list of them
def last(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case Con{h, Nil{}}:
      h
    case Con{_h, t}:
      last(t)

# the last thing a program said, which for one that reports as it goes is its
# answer
def tail(+out: String) -> String:
  last(String.lines(R.text(out)))

# the nth of a list of strings, or "" when there is no such one. The list and
# the count are scrutinised together, so the walk needs no helper to branch.
def nth(ls: List<&2, String>, n: Nat) -> String:
  match ls n:
    case Nil{} _m:
      ""
    case Con{h, _t} 0n:
      h
    case Con{_h, t} 1n+p:
      nth(t, p)

# the first line that starts with this, or "" when none does
def starting(ls: List<&2, String>, +pre: String) -> String:
  match ls:
    case []:
      ""
    case +h <> t:
      Bool.pick(String, String.starts_with(h, pre), h, starting(t, pre))

# the first line that holds this anywhere in it, or "" when none does
def containing(ls: List<&2, String>, +sub: String) -> String:
  match ls:
    case []:
      ""
    case +h <> t:
      Bool.pick(String, String.contains(h, sub), h, containing(t, sub))

# the last line that starts with this, or "" when none does. A build's answer
# is the last thing it says, because its log arrives on the same stream.
def starting.last(ls: List<&2, String>, +pre: String, got: String) -> String:
  match ls:
    case []:
      got
    case +h <> t:
      starting.last(t, pre, Bool.pick(String, String.starts_with(h, pre), h, got))

# what a `key = "value"` line holds, which is all ez's own files ever hold
def quoted(+l: String) -> String:
  nth(String.split(l, '"'), 1n)

# the value a text gives a key, over its `key = "value"` lines
def value(+text: String, +key: String) -> String:
  quoted(starting(String.lines(text), key))

# the directory the test is running in, which is the repo `ez test` was run from
def here() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["pwd"])
    return line(out)

# a fresh empty directory, removed when the test is done with it
def tmp() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["mktemp", "-d"])
    return line(out)

# a directory, and every directory above it
def mkdir(at: String) -> IO(Unit):
  do IO<Unit>:
    _o : String <- R.exec(["mkdir", "-p", at])
    return Unit{}

# a directory and everything under it, gone
def rm(at: String) -> IO(Unit):
  do IO<Unit>:
    _o : String <- R.exec(["rm", "-rf", at])
    return Unit{}

# a command run in a directory, with the gate's BEND_LIB taken away. Base has
# no chdir, so the directory is `env`'s business; and a test that is about
# where packages come from must not inherit the one the gate set for itself.
def inside(at: String, args: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, ["env", "-C", at, "-u", "BEND_LIB"], args)

# a TCP port nothing is listening on, so a stray server elsewhere can never
# answer for the one this test started
def port() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["python3", "-c",
      "import socket; s=socket.socket(); s.bind((\"127.0.0.1\", 0)); " ++
      "print(s.getsockname()[1]); s.close()"])
    return line(out)

# a program started and left running, and the pid it was given. `R.exec` waits
# for what it runs and reads it to the end, which a server never reaches, so
# this is the other effect.
def spawn(args: List<&2, String>) -> IO(String):
  R.start(args)

# a started program stopped again, by the pid it was started with, so a test
# can never stop anything but what it started
def stop(pid: String) -> IO(Unit):
  do IO<Unit>:
    _o : String <- R.exec(["kill", pid])
    return Unit{}

# a command retried until it answers or the tries run out: how a test waits for
# the server it just started. The verdict and the count are scrutinised
# together, so one def covers both endings and nothing recurses mutually.
def until(+args: List<&2, String>, n: Nat, ok: Bool) -> IO(Bool):
  match n ok:
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
def ready(args: List<&2, String>) -> IO(Bool):
  until(args, 100n, False{})

# run/run: the foreign effects, every one of them a program run with its
# arguments.
#
# Bend links its binaries with exactly `-lpthread -lm` (and X11 or alsa when the
# generated C includes their headers), so a TLS library cannot be linked in and
# the hub's HTTPS cannot be spoken from C. The programs that already speak HTTPS
# and git are on the PATH, so ez runs those instead of reimplementing them. One
# effect covers both. The second exists only because the first waits: a test
# that needs a server running beside it cannot wait for the server. The third
# exists because the first waits for one program at a time, and a gate holding
# thirty independent compiles should not.
import Base
import ../io/file.bend as F

# the program and its arguments, newline separated, run with no shell between.
# The answer is the exit status on its own first line, then stdout and stderr.
def ezrun.exec(cmd: String) -> IO(String):
  import "./exec.c"
  import "./exec.js"

# a program started and left running, answering with its pid. The effect above
# waits for what it runs and reads it to the end, which a server never reaches;
# this one waits for nothing, and gives the child a session and a /dev/null of
# its own so it holds no pipe open behind it.
def ezrun.start(cmd: String) -> IO(String):
  import "./start.c"
  import "./start.js"

# several programs run at once, answering with every exit status in the order
# the jobs were given. The children write into a directory rather than down a
# pipe, and `par` below reads those files back, so this answers statuses alone.
def ezrun.par(cmd: String) -> IO(String):
  import "./par.c"
  import "./par.js"

# the arguments as the effect wants them. Newline separated and execvp'd
# directly, so no argument is ever read as shell syntax.
def cmd(args: List<&2, String>) -> String:
  String.join(args, "\n")

# a program run with its arguments
def exec(args: List<&2, String>) -> IO(String):
  ezrun.exec(cmd(args))

# the strings that are not empty, which is what a list of statuses amounts to
# once a trailing newline has been counted as a line
def nonblank(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +more = nonblank(t)
      Bool.pick(List<&2, String>, String.is_empty(h), more, h <> more)

# how many strings there are
def count(ls: List<&2, String>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{_h, t}:
      (1n + count(t) : Nat)

# one job as the effect wants it: how many arguments, then each of them. The
# count is what lets an argument hold anything a line may hold, so no separator
# between jobs has to be invented and then kept out of the arguments.
def job(+args: List<&2, String>) -> String:
  Nat.show(count(args)) ++ "\n" ++ cmd(args)

# the jobs in the order they were given, each behind the newline that ends the
# field before it
def plan.go(js: List<&2, List<&2, String>>) -> String:
  match js:
    case Nil{}:
      ""
    case Con{h, t}:
      "\n" ++ job(h) ++ plan.go(t)

# what the effect is handed: how many may run at once, how many gigabytes each
# was given, where they write, and then every job
def plan(js: List<&2, List<&2, String>>, +width: String, +gb: String,
  +at: String) -> String:
  String.join([width, gb, at], "\n") ++ plan.go(js)

# a program started with its arguments and left running; the answer is its pid
def start(args: List<&2, String>) -> IO(String):
  ezrun.start(cmd(args))

# one job's answer, in the shape `exec` gives: the status on its own first
# line, then everything the program printed, read back out of the file it was
# pointed at
def par.of(+code: String, m: Maybe<&2, String>) -> String:
  code ++ "\n" ++ F.text_of(m)

# every job's answer, paired with the file it wrote by its place in the order
def par.read(cs: List<&2, String>, +at: String, +i: Nat) -> IO(List<&2, String>):
  match cs:
    case Nil{}:
      IO.pure(List<&2, String>, Nil{})
    case Con{+h, t}:
      do IO<List<&2, String>>:
        src : Maybe<&2, String> <- F.read(at ++ "/" ++ Nat.show(i))
        +more : List<&2, String> <- par.read(t, at, (1n + i : Nat))
        return par.of(h, src) <> more

# several programs run at once, each answered exactly as `exec` answers one, in
# the order the jobs were given. `at` is a directory the caller owns and this
# fills: job n writes to `at/n`, which is also where to look when one of them
# did something surprising. A width of "" leaves the count to the effect, which
# reads the cores and divides them by `gb`, the memory cap each job runs under.
def par(js: List<&2, List<&2, String>>, +width: String, +gb: String,
  +at: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    +out : String <- ezrun.par(plan(js, width, gb, at))
    par.read(nonblank(String.lines(out)), at, 0n)

# the first line of an answer, which is the exit status
def code.of(ls: List<&2, String>) -> String:
  match ls:
    case []:
      "127"
    case h <> t:
      h

# everything after the first line, which is what the program printed
def text.of(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> t:
      String.join(t, "\n")

# the exit status a run answered with
def code(out: String) -> String:
  code.of(String.lines(out))

# what the program printed, stdout and stderr together
def text(out: String) -> String:
  text.of(String.lines(out))

# a run that finished with status 0
def ok(+out: String) -> Bool:
  String.eq(code(out), "0")

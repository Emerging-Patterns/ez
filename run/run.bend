# run/run: the foreign effects, both of them a program run with its arguments.
#
# Bend links its binaries with exactly `-lpthread -lm` (and X11 or alsa when the
# generated C includes their headers), so a TLS library cannot be linked in and
# the hub's HTTPS cannot be spoken from C. The programs that already speak HTTPS
# and git are on the PATH, so ez runs those instead of reimplementing them. One
# effect covers both. The second effect exists only because the first waits:
# a test that needs a server running beside it cannot wait for the server.
import Base

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

# the arguments as the effect wants them. Newline separated and execvp'd
# directly, so no argument is ever read as shell syntax.
def cmd(args: List<&2, String>) -> String:
  String.join(args, "\n")

# a program run with its arguments
def exec(args: List<&2, String>) -> IO(String):
  ezrun.exec(cmd(args))

# a program started with its arguments and left running; the answer is its pid
def start(args: List<&2, String>) -> IO(String):
  ezrun.start(cmd(args))

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

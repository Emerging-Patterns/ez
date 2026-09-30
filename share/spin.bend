# share/spin: the mark drawn while a long step runs. The words are
# share/say.bend. The mark is a child, because the work itself is one program
# waited on to the end and nothing can be printed while it runs.
import Base
import 0xabe575924687afad4cee1a2c1194d639/main.bend as R
import ./say.bend as Say

# the parent's fd, by number. The child cannot look at its own: that one was
# replaced with a pipe before this ran. `$1` is the number.
def probe() -> String:
  "ppid=; while read -r k v; do case $k in PPid:) ppid=$v;; esac; done < /proc/self/status; readlink /proc/$ppid/fd/$1 2>/dev/null"

# a mark on the terminal while the parent is alive. `$1` is the terminal,
# `$2` the line. The mark walks ⠋ ⠙ ⠹ ⠸ ⠼ ⠴ ⠦ ⠧ ⠇ ⠏. An empty parent
# id exits rather than spinning on `/proc`.
def frames() -> String:
  "ppid=; while read -r k v; do case $k in PPid:) ppid=$v;; esac; done < /proc/self/status; [ -n \"$ppid\" ] || exit 0; while [ -d /proc/$ppid ]; do printf '\\r%s %s' '⠋' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠙' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠹' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠸' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠼' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠴' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠦' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠧' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠇' \"$2\" >\"$1\"; sleep 0.08; [ -d /proc/$ppid ] || break; printf '\\r%s %s' '⠏' \"$2\" >\"$1\"; sleep 0.08; done"

# the mark wiped, and the line left in its place
def settle() -> String:
  "printf '\\r\\033[K%s\\n' \"$2\" >\"$1\""

# one fd of this process, as a path. A failure is not a terminal.
def link(+fd: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["sh", "-c", probe(), "sh", fd])
    return String.trim(R.text(out))

# the terminal this process writes to, stderr's first, or empty for none
def dev() -> IO(String):
  do IO<String>:
    +err : String <- link("2")
    +out : String <- link("1")
    return Say.tty.pick(err, out)

# the mark, when there is a terminal to draw it on
def start(on: Bool, +dev: String, +msg: String) -> IO(Say.Spin):
  match on:
    case False{}:
      IO.pure(Say.Spin, Say.Spin{"", "", ""})
    case True{}:
      do IO<Say.Spin>:
        +pid : String <- R.start(["sh", "-c", frames(), "sh", dev, msg])
        return Say.Spin{dev, String.trim(pid), msg}

def hold.at(plain: Bool, +dev: String, +msg: String) -> IO(Say.Spin):
  match plain:
    case True{}:
      do IO<Say.Spin>:
        IO.print_err(msg)
        return Say.Spin{"", "", ""}
    case False{}:
      start(True{}, dev, msg)

# the line, then the mark when a terminal will show it moving. A pipe gets
# the line and nothing else.
def hold(+msg: String) -> IO(Say.Spin):
  do IO<Say.Spin>:
    +tty : String <- dev()
    hold.at(String.is_empty(tty), tty, msg)

# a spinner that never started still owes its line, unless the plain path
# already printed it and left the message empty
def owed(empty: Bool, +msg: String) -> IO(Unit):
  match empty:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print_err(msg)

# the mark stopped, and the line written where it was
def done.live(+dev: String, +pid: String, +msg: String) -> IO(Unit):
  do IO<Unit>:
    _k : String <- R.exec(["kill", pid])
    _s : String <- R.exec(["sh", "-c", settle(), "sh", dev, msg])
    return Unit{}

def done.bad(bad: Bool, +dev: String, +pid: String, +msg: String) -> IO(Unit):
  match bad:
    case True{}:
      owed(String.is_empty(msg), msg)
    case False{}:
      done.live(dev, pid, msg)

# the step finished: the mark stopped and the line left, or the line owed
def done(spin: Say.Spin) -> IO(Unit):
  Say.Spin{+term, +pid, +msg} = spin
  done.bad(Bool.or(String.is_empty(pid), String.eq(pid, "0")), term, pid, msg)

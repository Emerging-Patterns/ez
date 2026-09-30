# share/spin: the spinner share/say's words are drawn with. This is the half
# that runs programs: it asks which terminal this process writes to, starts
# the mark as a child and stops it. It lives apart from the words because a
# program runs through snap's foreign effect, and bend 2.0.32 fails a proof
# whose imports reach foreign code, so a law may import share/say but never
# this.
import Base
import 0xabe575924687afad4cee1a2c1194d639/main.bend as R
import ./say.bend as Say

# one fd of this process, as a path. A failure is not a terminal.
def link(+fd: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["sh", "-c", Say.probe(), "sh", fd])
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
        +pid : String <- R.start(["sh", "-c", Say.frames(), "sh", dev, msg])
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
    _s : String <- R.exec(["sh", "-c", Say.settle(), "sh", dev, msg])
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

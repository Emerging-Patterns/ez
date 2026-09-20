# lanes: native
# run.par: several programs run at once. The other two effects run one program;
# this one runs a list of them and answers each the way `exec` answers one, in
# the order they were given.
#
# The header hands this to the native lane alone, and the overlap check is why.
# The JS twin runs the jobs in turn — node cannot wait on several children from
# inside a synchronous effect — so the lane that would prove them concurrent is
# the one that is not. What both lanes do promise is the answers, and those are
# checked here too.
import Base
import ../../run/run.bend as R
import ../../check/kit.bend as Check
import ../../check/world.bend as W
import ../../io/file.bend as F

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# the nth answer of a batch, or "" when the batch was shorter than that
def nth(rs: List<&2, String>, n: Nat) -> String:
  match rs n:
    case Nil{} _m:
      ""
    case Con{h, _t} 0n:
      h
    case Con{_h, t} 1n+p:
      nth(t, p)

# what a batch of ordinary jobs answers: a status and an output each, in the
# order the jobs were given and never in the order they happened to finish
def answers(+at: String) -> IO(Unit):
  do IO<Unit>:
    +rs : List<&2, String> <- R.par([["echo", "one two"], ["false"],
      ["ez-no-such-program"], ["echo", "$HOME;ls"]], "", "8", at)
    Check.eq_str("a job's output comes back with it", R.text(nth(rs, 0n)),
      "one two\n")
    Check.eq_str("and its status", R.code(nth(rs, 0n)), "0")
    Check.eq_str("a failing job answers its own status", R.code(nth(rs, 1n)),
      "1")
    Check.eq_str("a job that is not there answers 127", R.code(nth(rs, 2n)),
      "127")
    Check.eq_str("no shell reads the arguments", R.text(nth(rs, 3n)),
      "$HOME;ls\n")

# whether the jobs really did overlap. One of them blocks on a fifo nothing has
# opened for writing yet, and the other is what opens it. Run at once, the
# reader is handed the word and exits 0; run in turn, it waits out its timeout
# and answers 124 instead, so the check cannot pass on a sequential run.
#
# Both jobs are bounded, and the writer's bound is the one easy to forget:
# opening a fifo for writing blocks until someone opens it for reading, so a
# sequential runner that had already given up on the reader would hang here
# rather than fail. A test that hangs says nothing.
def overlap(+at: String) -> IO(Unit):
  do IO<Unit>:
    _f : String <- R.exec(["mkfifo", at ++ "/f"])
    W.mkdir(at ++ "/out")
    +rs : List<&2, String> <- R.par([["timeout", "5", "cat", at ++ "/f"],
      ["timeout", "5", "cp", at ++ "/word", at ++ "/f"]], "", "8",
      at ++ "/out")
    Check.eq_str("a job that waits on another is run beside it, not after it",
      R.text(nth(rs, 0n)), "overlapped\n")
    yes("and it is not the timeout that ended it",
      String.eq(R.code(nth(rs, 0n)), "0"))

def go(+at: String) -> IO(Unit):
  do IO<Unit>:
    _w : Bool <- F.write(at ++ "/word", "overlapped\n")
    answers(at)
    overlap(at)
    W.rm(at)

def main() -> IO(Unit):
  do IO<Unit>:
    at : String <- W.tmp()
    go(at)

#|ok a job's output comes back with it
#|ok and its status
#|ok a failing job answers its own status
#|ok a job that is not there answers 127
#|ok no shell reads the arguments
#|ok a job that waits on another is run beside it, not after it
#|ok and it is not the timeout that ended it

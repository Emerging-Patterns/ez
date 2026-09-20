# run.start: a program left running. The other effect waits for what it runs
# and reads it to the end; this one hands back a pid and returns at once, which
# is the only way a test can have a server beside it.
import Base
import ../../run/run.bend as R
import ../../check/kit.bend as Check
import ../../check/world.bend as W

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# what was started, once the pid and the scratch file are known
def go(+at: String) -> IO(Unit):
  do IO<Unit>:
    _t : String <- W.spawn(["touch", at ++ "/ran"])
    +saw : Bool <- W.ready(["test", "-f", at ++ "/ran"])
    yes("a started program runs, with nothing waiting for it", saw)
    +pid : String <- W.spawn(["sleep", "30"])
    +ps : String <- R.exec(["ps", "-o", "args=", "-p", pid])
    yes("the pid it answers with names that program",
      String.contains(R.text(ps), "sleep 30"))
    W.stop(pid)
    W.rm(at)

def main() -> IO(Unit):
  do IO<Unit>:
    at : String <- W.tmp()
    go(at)

#|ok a started program runs, with nothing waiting for it
#|ok the pid it answers with names that program

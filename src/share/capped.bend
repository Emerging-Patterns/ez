# share/capped: the words of a run under the memory cap share/cap sets, and
# what is said of a run the cap killed. They are apart from share/cap, which
# runs programs through snap's foreign effect, so that a law may import them
# (laws/CappedRunWords.bend).
import Base
import snap@1.4.0.0/src/answer.bend as R
import ./env.bend as Env

# the cgroup a capped run gets. `MemorySwapMax=0` matters: without it the
# cgroup spills into swap and the cap stops meaning anything.
def scope(+gigs: String) -> List<&2, String>:
  ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=" ++ gigs ++ "G",
    "-p", "MemorySwapMax=0", "nice"]

# the words a capped run is prefixed with, or none when nothing can cap it
def pre(on: Bool, +gigs: String) -> List<&2, String>:
  match on:
    case True{}:
      scope(gigs)
    case False{}:
      []

# a program's arguments dressed the way the cap wants them, for a caller that
# is not going to run it here. The cap goes outside `env`, so the variable is
# set inside the cgroup.
def argv(on: Bool, +gigs: String, +at: String, args: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, pre(on, gigs), Env.line(at, args))

# the status the kernel leaves on a process it killed for memory
def killed(+out: String) -> Bool:
  String.eq(R.code(out), "137")

# what to say when a run died for memory rather than for being wrong
def why(+out: String, +gigs: String) -> String:
  Bool.pick(String, killed(out),
    "killed for memory at " ++ gigs ++ "G: raise EZ_CAP\n", "")

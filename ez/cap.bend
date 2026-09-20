# ez/cap: every `bend` the runner starts, inside a memory cap.
#
# bend's C backend, not clang, is what costs the memory: emitting the C for a
# large program peaked at 18.8 GB here while clang on that same C peaked at
# 242 MB. An uncapped run reached 35 GB and took the host down. Worse, bend
# prints that all terms check *before* it emits any C, so a build the kernel
# kills for memory looks exactly like one that succeeded and happened to write
# no binary. The cap is what turns that into a legible exit 137.
import Base
import ../run/run.bend as R
import ./env.bend as Env
import ./args.bend as Args

# how many gigabytes one `bend` may have. 8 is what fits beside the rest of
# this machine; a project whose closure costs more says so in EZ_CAP.
def gb() -> IO(String):
  Env.var("EZ_CAP", "8")

# whether systemd-run is here to do the capping. A missing program fails the
# exec rather than the run, so this asks once and the caller carries the answer.
def ok() -> IO(Bool):
  do IO<Bool>:
    +out : String <- R.exec(["systemd-run", "--version"])
    return R.ok(out)

# the cgroup a capped run gets. `MemorySwapMax=0` matters: without it the
# cgroup spills into swap and the cap stops meaning anything.
def scope(+g: String) -> List<&2, String>:
  ["systemd-run", "--user", "--scope", "-q", "-p", "MemoryMax=" ++ g ++ "G",
    "-p", "MemorySwapMax=0", "nice"]

# the words a capped run is prefixed with, or none when nothing can cap it
def pre(on: Bool, +g: String) -> List<&2, String>:
  match on:
    case True{}:
      scope(g)
    case False{}:
      []

# a program run under the cap, with this project's BEND_LIB set for it. The
# cap goes outside `env`, so the variable is set inside the cgroup.
def run(on: Bool, args: List<&2, String>) -> IO(String):
  do IO<String>:
    +g : String <- gb()
    at : String <- Env.lib()
    R.exec(List.append(&2, String, pre(on, g), Env.line(at, args)))

# the status the kernel leaves on a process it killed for memory
def killed(+out: String) -> Bool:
  String.eq(R.code(out), "137")

# what to say when a run died for memory rather than for being wrong
def why(+out: String, +g: String) -> String:
  Bool.pick(String, killed(out),
    "killed for memory at " ++ g ++ "G: raise EZ_CAP\n", "")

# a warning printed once when nothing is capping the jobs
def warn(on: Bool) -> IO(Unit):
  match on:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.write("warning: systemd-run is not here, so no `bend` is capped\n")

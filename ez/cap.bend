# ez/cap: every `bend` the runner starts, inside a memory cap.
#
# bend's C backend, not clang, is what costs the memory: emitting the C for a
# large program peaked at 18.8 GB here while clang on that same C peaked at
# 242 MB. An uncapped run reached 35 GB and took the host down. Worse, bend
# prints that all terms check *before* it emits any C, so a build the kernel
# kills for memory looks exactly like one that succeeded and happened to write
# no binary. The cap is what turns that into a legible exit 137.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../ez/env.bend as Env
import ../ez/args.bend as Args

# how many gigabytes one `bend` may have. 8 is what fits beside the rest of
# this machine; a project whose closure costs more says so in EZ_CAP.
#
# The cap is also the divisor the gate picks its width from, since a run has to
# assume every job it starts at once could want the whole of it. So a cap set
# higher than a tree needs does not only reserve memory, it narrows the gate:
# the dearest aggregate here peaks at 3.3G, and at the 8G cap that is a width
# of 4 where 11 would fit. Lower EZ_CAP, or set EZ_JOBS outright, for a tree
# you have measured.
def gb() -> IO(String):
  Env.var("EZ_CAP", "8")

# whether a `bend` can be capped. The cap is `systemd-run --user`. That
# fails when the program is absent, and it fails when the program is present
# and the user bus is not. Either failure is no cap. A probe that would
# wait on a password fails closed instead.
def ok() -> IO(Bool):
  do IO<Bool>:
    +out : String <- R.exec(["systemd-run", "--user", "--scope", "-q",
      "--collect", "--no-ask-password", "true"])
    return R.ok(out)

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

# a program run under the cap, with this project's BEND_LIB set for it
def run(on: Bool, args: List<&2, String>) -> IO(String):
  do IO<String>:
    +g : String <- gb()
    at : String <- Env.lib()
    R.exec(argv(on, g, at, args))

# the status the kernel leaves on a process it killed for memory
def killed(+out: String) -> Bool:
  String.eq(R.code(out), "137")

# what to say when a run died for memory rather than for being wrong
def why(+out: String, +gigs: String) -> String:
  Bool.pick(String, killed(out),
    "killed for memory at " ++ gigs ++ "G: raise EZ_CAP\n", "")

# what is said when nothing is capping the jobs
def warning() -> String:
  "warning: systemd-run --user cannot cap `bend`, so no `bend` is capped"

# a warning printed once when nothing is capping the jobs
def warn(on: Bool) -> IO(Unit):
  match on:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.write(warning() ++ "\n")

# the same warning on stderr, for a command whose stdout is the program's
def warn.err(on: Bool) -> IO(Unit):
  match on:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.print_err(warning())

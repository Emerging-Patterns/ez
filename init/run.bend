# init/run: the interpreter for `ez init`. It reads ez.toml, `.gitignore`,
# the entry file and `src/lib.bend` into a World, asks the planner
# (init/plan.bend) for the plan, and runs it with the lock's effect runner
# (`Run.exec.plan`), which makes a file's directory before writing it and
# exits 1 with the reason when the plan refuses. It decides nothing; that it
# reads and executes faithfully is EZ-TRUST-2.
import Base
import ../io/file.bend as F
import ../lock/run.bend as Run
import ./plan.bend as IP

# `ez init [name] [entry.bend] [--description TEXT]`
def run(+name: String, +file: String, +desc: String) -> IO(Unit):
  do IO<Unit>:
    lib : String <- Run.bend.lib()
    led : Maybe<&2, String> <- F.read(IP.toml())
    ig : Maybe<&2, String> <- F.read(IP.ignore.file())
    mn : Maybe<&2, String> <- F.read(IP.entry.or(file))
    lb : Maybe<&2, String> <- F.read(IP.lib.file())
    Run.exec.plan(lib, IP.plan(IP.World{name, file, desc, led, ig, mn, lb}))

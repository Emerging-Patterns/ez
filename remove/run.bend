# remove/run: the interpreter for `ez remove`. It reads ez.toml and
# `.gitignore` into a World, asks the planner (remove/plan.bend) for the plan,
# and runs it with the lock's effect runner (`Run.exec.plan`), which exits 1
# with the reason when the plan refuses. It decides nothing; that it reads and
# executes faithfully is EZ-TRUST-2.
import Base
import ../io/file.bend as F
import ../lock/run.bend as Run
import ./plan.bend as RP

# `ez remove <name>`
def run(+name: String) -> IO(Unit):
  do IO<Unit>:
    lib : String <- Run.bend.lib()
    led : Maybe<&2, String> <- F.read(RP.toml())
    ig : Maybe<&2, String> <- F.read(RP.ignore.file())
    Run.exec.plan(lib, RP.plan(RP.World{name, led, F.text_of(ig)}))

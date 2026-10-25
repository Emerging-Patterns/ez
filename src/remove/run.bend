# remove/run: the interpreter for `ez remove`. It reads the directory it runs
# in, ez.toml, `.gitignore` and the `.bend` files git lists into a World, then
# loops: it asks the planner (remove/relock.bend) what the lock after the
# remove still needs, answers each question with the lock's interpreter
# (`Run.answer.all`), and adds the answers to the World, until nothing is
# left to ask. Then it runs the plan with the lock's effect runner
# (`Run.exec.plan`), which exits 1 with the reason when the plan refuses. It
# decides nothing; that it reads and executes faithfully is EZ-TRUST-2.
import Base
import 0x8e26a6f8c31689519e618374376ee3dd/main.bend as R
import ../io/file.bend as F
import ../lock/run.bend as Run
import ../lock/world.bend as W
import ./plan.bend as RP
import ./relock.bend as RR
import ../ws/relock.bend as Rel
import ../ws/run.bend as WsRun

# the World with more of the lock's answers in it
def more(world: RR.World, rs: List<&2, W.Reply>) -> RR.World:
  RR.World{r, here, listing, locks} = world
  RR.World{r, here, listing, List.append(&2, W.Reply, locks, rs)}

# the planner's step: its questions answered and the loop gone round again,
# or its plan run
def loop.step(st: RR.Next, +lib: String, world: RR.World, go: RR.World -> IO(Unit)) -> IO(Unit):
  match st:
    case RR.AskLock{asks}:
      do IO<Unit>:
        rs : List<&2, W.Reply> <- Run.answer.all(lib, asks)
        go(more(world, rs))
    case RR.Planned{pl}:
      Run.exec.plan(lib, pl)

# the loop, under fuel. Every round adds an answer, since the lock never asks
# what the World answers already, so the fuel (`Run.rounds`) is only a guard.
def loop(fuel: Nat, +lib: String, +ws: Rel.Ws, +world: RR.World) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "ez: ez remove kept asking questions")
    case 1n+f:
      loop.step(Rel.remove.next(ws, world), lib, world, w => loop(f, lib, ws, w))

# `ez remove <name>`
def run(+name: String) -> IO(Unit):
  do IO<Unit>:
    lib : String <- Run.bend.lib()
    +pwd : String <- R.exec(["pwd"])
    led : Maybe<&2, String> <- F.read(RP.toml())
    ig : Maybe<&2, String> <- F.read(RP.ignore.file())
    ls : W.Listing <- Run.read.listing()
    ws : Rel.Ws <- WsRun.relock.ws()
    loop(Run.rounds(), lib, ws, RR.World{RP.World{name, led, F.text_of(ig)},
      String.trim(R.text(pwd)), ls, []})

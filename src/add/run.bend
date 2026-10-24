# add/run: the interpreter for `ez add`. It reads the directory it runs in,
# HOME, ez.toml, `.gitignore` and the `.bend` files git lists into a World,
# then loops: it asks the planner (add/relock.bend) what is still open,
# answers each question with the lock's interpreter (`Run.answer.ups`: what
# git prints for tags, HEAD or a ref, and a checkout at a rev with its NAR
# hash and every file's text; `Run.answer.all`: for a hub package's name,
# what the hub says the name names, and the package's manifest and files,
# and for the lock that follows the add, each package and name it reads, as
# `ez lock` answers them), and adds the answers to the World, until nothing
# is left to ask. Then it runs the planner's plan with the lock's effect
# runner (`Run.exec.plan`), which exits 1 with the reason when the plan
# refuses. It decides nothing; that it reads and executes faithfully is
# EZ-TRUST-2.
import Base
import 0xead4c7939c9eaca8d47da53b4496b731/main.bend as R
import ../io/file.bend as F
import ../lock/run.bend as Run
import ../lock/up.bend as Up
import ../lock/world.bend as W
import ./world.bend as A
import ../ws/run.bend as WsRun
import ./relock.bend as AR
import ../ws/relock.bend as Rel

# the World with more answers in it
def more(world: AR.World, rs: List<&2, Up.Reply>) -> AR.World:
  AR.World{A.World{args, here, home, ledger, ignore, replies, hubs}, listing, locks} = world
  AR.World{A.World{args, here, home, ledger, ignore, List.append(&2, Up.Reply, replies, rs), hubs},
    listing, locks}

# the World with more of the hub's answers in it
def more.hub(world: AR.World, rs: List<&2, W.Reply>) -> AR.World:
  AR.World{A.World{args, here, home, ledger, ignore, replies, hubs}, listing, locks} = world
  AR.World{A.World{args, here, home, ledger, ignore, replies, List.append(&2, W.Reply, hubs, rs)},
    listing, locks}

# the World with more of the lock's answers in it
def more.lock(world: AR.World, rs: List<&2, W.Reply>) -> AR.World:
  AR.World{a, listing, locks} = world
  AR.World{a, listing, List.append(&2, W.Reply, locks, rs)}

# the planner's step: its questions answered and the loop gone round again,
# or its plan run
def loop.step(st: AR.Next, +lib: String, world: AR.World, go: AR.World -> IO(Unit)) -> IO(Unit):
  match st:
    case AR.AskGit{asks}:
      do IO<Unit>:
        rs : List<&2, Up.Reply> <- Run.answer.ups(lib, asks)
        go(more(world, rs))
    case AR.AskHub{asks}:
      do IO<Unit>:
        rs : List<&2, W.Reply> <- Run.answer.all(lib, asks)
        go(more.hub(world, rs))
    case AR.AskLock{asks}:
      do IO<Unit>:
        rs : List<&2, W.Reply> <- Run.answer.all(lib, asks)
        go(more.lock(world, rs))
    case AR.Planned{pl}:
      Run.exec.plan(lib, pl)

# the rounds the loop may take. The add asks at most three rounds for a git
# target and two for a name; the lock after it asks a round per level of the
# import graph, as `ez lock` does (`Run.rounds`). This is only a guard against
# a planner that keeps asking, and running out of it dies loudly.
def rounds() -> Nat:
  U32.to_nat(100000)

# the loop, under fuel. Every round adds an answer, since the planner never
# asks what the World answers already, so the fuel is only a guard.
def loop(fuel: Nat, +lib: String, +ws: Rel.Ws, +world: AR.World) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "ez: ez add kept asking questions")
    case 1n+f:
      loop.step(Rel.add.next(ws, world), lib, world, w => loop(f, lib, ws, w))

# `ez add <target> [ref] [entry.bend] [--rename NAME]`
def run(+target: String, +ref: String, +entry: String, +rename: String) -> IO(Unit):
  do IO<Unit>:
    lib : String <- Run.bend.lib()
    +pwd : String <- R.exec(["pwd"])
    h : Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    +home : String <- IO.pure(String, Run.env.text(h))
    pinned : String <- WsRun.add.ref(home, target, ref)
    led : Maybe<&2, String> <- F.read(A.toml())
    ig : Maybe<&2, String> <- F.read(A.ignore.file())
    ls : W.Listing <- Run.read.listing()
    ws : Rel.Ws <- WsRun.relock.ws()
    loop(rounds(), lib, ws, AR.World{A.World{A.Args{target, pinned, entry, rename},
      String.trim(R.text(pwd)), home, led, F.text_of(ig), [], []}, ls, []})

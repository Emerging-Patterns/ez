# add/run: the interpreter for `ez add`. It reads the directory it runs in,
# HOME, ez.toml and `.gitignore` into a World, then loops: it asks the
# planner (add/plan.bend) what is still open, answers each question with the
# lock's interpreter (`Run.answer.ups`: what git prints for tags, HEAD or a
# ref, and a checkout at a rev with its NAR hash and every file's text; for a
# hub package's name, `Run.answer.all`: what the hub says the name names, and
# the package's manifest and files), and adds the answers to the World, until
# nothing is left to ask. Then it runs
# the planner's plan with the lock's effect runner (`Run.exec.plan`), which
# exits 1 with the reason when the plan refuses. It decides nothing; that it
# reads and executes faithfully is EZ-TRUST-2.
import Base
import 0x103d0af04de36ab98b311e537366ec67/main.bend as R
import ../io/file.bend as F
import ../lock/run.bend as Run
import ../lock/up.bend as Up
import ../lock/world.bend as W
import ./world.bend as A
import ./plan.bend as AP

# the World with more answers in it
def more(world: A.World, rs: List<&2, Up.Reply>) -> A.World:
  A.World{args, here, home, ledger, ignore, replies, hubs} = world
  A.World{args, here, home, ledger, ignore, List.append(&2, Up.Reply, replies, rs), hubs}

# the World with more of the hub's answers in it
def more.hub(world: A.World, rs: List<&2, W.Reply>) -> A.World:
  A.World{args, here, home, ledger, ignore, replies, hubs} = world
  A.World{args, here, home, ledger, ignore, replies, List.append(&2, W.Reply, hubs, rs)}

# the planner's step: its questions answered and the loop gone round again,
# or its plan run
def loop.step(st: AP.Next, +lib: String, world: A.World, go: A.World -> IO(Unit)) -> IO(Unit):
  match st:
    case AP.AskGit{asks}:
      do IO<Unit>:
        rs : List<&2, Up.Reply> <- Run.answer.ups(lib, asks)
        go(more(world, rs))
    case AP.AskHub{asks}:
      do IO<Unit>:
        rs : List<&2, W.Reply> <- Run.answer.all(lib, asks)
        go(more.hub(world, rs))
    case AP.Done{pl}:
      Run.exec.plan(lib, pl)

# the loop, under fuel. Every round adds an answer, since the planner never
# asks what the World answers already, and it asks at most three rounds for
# a git target and two for a name, so the fuel is only a guard.
def loop(fuel: Nat, +lib: String, +world: A.World) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "ez: ez add kept asking questions")
    case 1n+f:
      loop.step(AP.next(world), lib, world, w => loop(f, lib, w))

# `ez add <target> [ref] [entry.bend] [--rename NAME]`
def run(+target: String, +ref: String, +entry: String, +rename: String) -> IO(Unit):
  do IO<Unit>:
    lib : String <- Run.bend.lib()
    +pwd : String <- R.exec(["pwd"])
    h : Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    led : Maybe<&2, String> <- F.read(A.toml())
    ig : Maybe<&2, String> <- F.read(A.ignore.file())
    loop(U32.to_nat(100), lib, A.World{A.Args{target, ref, entry, rename}, String.trim(R.text(pwd)),
      Run.env.text(h), led, F.text_of(ig), [], []})

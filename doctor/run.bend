# doctor/run: the interpreter for `ez doctor`. It reads `$CC`, `$BEND_LIB`,
# the ledger's text and the lock's text into a World, then loops: it asks
# the planner (doctor/plan.bend) what is still open, answers each question,
# and adds the answers to the World, until nothing is left to ask. Then it
# runs the planner's plan with the lock's effect runner (`Run.exec.plan`),
# which prints each line and exits 1 when the plan fails the command.
#
# A version question runs the program with `--version`, except bend, which
# is asked through run/bend since it has answered the question two ways over
# its versions. The library is listed with `ls`, and the sources are read as
# `ez lock` reads them (`Run.read.listing`). None of these writes anything,
# and the plan writes nothing either. It decides nothing; that it reads and
# executes faithfully is EZ-TRUST-2.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../run/bend.bend as Bend
import ../io/file.bend as F
import ../ez/args.bend as Args
import ../lock/run.bend as Run
import ../lock/world.bend as W
import ./world.bend as DW
import ./plan.bend as DP

# how a program is asked for its version, once it is known whether this is
# bend. Everything else answers the flag.
def probe.ask(is_bend: Bool, name: String) -> IO(String):
  match is_bend:
    case True{}:
      Bend.version()
    case False{}:
      R.exec([name, "--version"])

# one question, answered
def answer(ask: DW.Ask) -> IO(DW.Answer):
  match ask:
    case DW.Probe{+name}:
      do IO<DW.Answer>:
        +out : String <- probe.ask(String.eq(name, "bend"), name)
        return DW.Printed{R.ok(out), R.text(out)}
    case DW.Lib{dir}:
      do IO<DW.Answer>:
        +out : String <- R.exec(["ls", dir])
        return DW.Printed{R.ok(out), R.text(out)}
    case DW.Sources{}:
      do IO<DW.Answer>:
        l : W.Listing <- Run.read.listing()
        return DW.Listed{l}

# every question, answered
def answer.all(asks: List<&2, DW.Ask>) -> IO(List<&2, DW.Reply>):
  match asks:
    case []:
      IO.pure(List<&2, DW.Reply>, [])
    case +h <> t:
      do IO<List<&2, DW.Reply>>:
        a : DW.Answer <- answer(h)
        rest : List<&2, DW.Reply> <- answer.all(t)
        return DW.Reply{h, a} <> rest

# the World with more answers in it
def more(world: DW.World, rs: List<&2, DW.Reply>) -> DW.World:
  DW.World{cc, lib, ledger, lock, replies} = world
  DW.World{cc, lib, ledger, lock, List.append(&2, DW.Reply, replies, rs)}

# the planner's step: its questions answered and the loop gone round again,
# or its plan run
def loop.step(st: DP.Step, world: DW.World, go: DW.World -> IO(Unit)) -> IO(Unit):
  match st:
    case DP.Asking{asks}:
      do IO<Unit>:
        rs : List<&2, DW.Reply> <- answer.all(asks)
        go(more(world, rs))
    case DP.Run{pl}:
      Run.exec.plan("", pl)

# the loop, under fuel. Every question depends only on what the World read,
# so one round answers them all, and the fuel is only a guard.
def loop(fuel: Nat, +world: DW.World) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "ez: ez doctor kept asking questions")
    case 1n+f:
      loop.step(DP.step(world), world, w => loop(f, w))

# a variable's text, "" when it is unset
def var(name: String) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env(name)
    return Args.text_of(r)

# `ez doctor`: the toolchain and the project, reported on
def run() -> IO(Unit):
  do IO<Unit>:
    cc : String <- var("CC")
    lib : String <- var("BEND_LIB")
    led : Maybe<&2, String> <- F.read(DW.toml())
    lk : Maybe<&2, String> <- F.read(DW.lockfile())
    loop(U32.to_nat(3), DW.World{cc, lib, led, lk, []})

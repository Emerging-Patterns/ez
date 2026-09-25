# pub/run: the interpreter for `ez publish`. It reads the directory the
# project is in and the ledger's text into a World, then loops: it asks the
# planner (pub/plan.bend) what is still open, answers each question, and adds
# the answers to the World, until nothing is left to ask. Then it runs the
# planner's plan with the lock's effect runner (`Run.exec.plan`), which prints
# what a publish that agreed says, or exits 1 with the reason.
#
# What git says of the project and a file's text are answered as the tool
# commands answer them (`ToolRun.answer`). What git tracks is `git ls-files
# -v` in the project, with paths written as they are rather than quoted. The
# upload is `bend <entry> --publish`, followed by the `<name>@<version>` the
# planner put in the question when the ledger names one, with the project's
# packages on BEND_LIB, the way every other `bend` ez starts has them; the
# planner asks for it last, once every other check has passed. Just before it
# runs, the line the question carries, the hub description, goes to stderr,
# where bend's own notices go, so stdout stays the hash and the import line.
# Before that, the lock is read as a file, and a url under the hub is asked
# for with the lock's own GET (`Web.get`), whose answer is a status line and
# the text: whether the hub answered 200, and the body or why not.
# It decides nothing; that it reads and executes faithfully is EZ-TRUST-2.
import Base
import 0x103d0af04de36ab98b311e537366ec67/main.bend as R
import ../io/file.bend as F
import ../lock/run.bend as Run
import ../tool/run.bend as ToolRun
import ../tool/world.bend as TW
import ../hub/hub.bend as Web
import ../ez/env.bend as Env
import ./world.bend as PW
import ./plan.bend as PP

# what a program printed, and whether it exited 0
def ran(+out: String) -> PW.Answer:
  PW.Ran{R.ok(out), R.text(out)}

# one question, answered
def answer(+lib: String, ask: PW.Ask) -> IO(PW.Answer):
  match ask:
    case PW.Tool{q}:
      do IO<PW.Answer>:
        a : TW.Answer <- ToolRun.answer(q)
        return PW.Told{a}
    case PW.Tracked{}:
      do IO<PW.Answer>:
        +out : String <- R.exec(["git", "-c", "core.quotePath=false", "ls-files", "-v"])
        return ran(out)
    case PW.Upload{+entry, +named, says}:
      do IO<PW.Answer>:
        IO.print_err(says)
        +out : String <- R.exec(Env.line(lib, PP.upload.line(entry, named)))
        return ran(out)
    case PW.Lock{}:
      do IO<PW.Answer>:
        m : Maybe<&2, String> <- F.read(PW.lockfile())
        return PW.Told{TW.Text{m}}
    case PW.Hub{+url}:
      do IO<PW.Answer>:
        +out : String <- Web.get(url)
        return ran(out)

# every question, answered
def answer.all(+lib: String, asks: List<&2, PW.Ask>) -> IO(List<&2, PW.Reply>):
  match asks:
    case []:
      IO.pure(List<&2, PW.Reply>, [])
    case +h <> t:
      do IO<List<&2, PW.Reply>>:
        a : PW.Answer <- answer(lib, h)
        rest : List<&2, PW.Reply> <- answer.all(lib, t)
        return PW.Reply{h, a} <> rest

# the World with more answers in it
def more(world: PW.World, rs: List<&2, PW.Reply>) -> PW.World:
  PW.World{here, ledger, replies} = world
  PW.World{here, ledger, List.append(&2, PW.Reply, replies, rs)}

# the planner's step: its questions answered and the loop gone round again,
# or its plan run
def loop.step(st: PP.Step, +lib: String, world: PW.World, go: PW.World -> IO(Unit)) -> IO(Unit):
  match st:
    case PP.Asking{asks}:
      do IO<Unit>:
        rs : List<&2, PW.Reply> <- answer.all(lib, asks)
        go(more(world, rs))
    case PP.Run{pl}:
      Run.exec.plan(lib, pl)

# the loop, under fuel. The walk asks for one file a round, so the fuel is a
# guard against a planner that keeps asking, not a limit on a package.
def loop(fuel: Nat, +lib: String, +world: PW.World) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "ez: ez publish kept asking questions")
    case 1n+f:
      loop.step(PP.step(world), lib, world, w => loop(f, lib, w))

# `ez publish`: the package the project's ledger names, checked, sent, and
# the hash bend answered checked against ez's own
def run() -> IO(Unit):
  do IO<Unit>:
    lib : String <- Env.lib()
    +pwd : String <- R.exec(["pwd"])
    led : Maybe<&2, String> <- F.read(PW.toml())
    loop(U32.to_nat(100000), lib, PW.World{String.trim(R.text(pwd)), led, []})

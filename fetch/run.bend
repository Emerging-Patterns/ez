# fetch/run: the interpreter for `ez fetch`. It reads whether there is an
# ez.toml and the lock's text into a World, with the directory they are in,
# then loops: it asks the planner (fetch/plan.bend) what is still open,
# answers each question, and adds the answers to the World, until nothing is
# left to ask. Then it runs the planner's plan with the lock's effect runner
# (`Run.exec.plan`), which lays each tree and exits 1 with the reason when
# the plan refuses. A tree under BEND_LIB is read here as the lock reads one
# (`Run.answer.lib`), a hub package is fetched as the lock fetches one
# (`Run.answer`), and a checkout is made as `ez add` makes one
# (`Run.answer.up` of `Up.Clone`), in a scratch directory outside the project
# and BEND_LIB that is removed whether or not the clone worked. A name's file
# under `BEND_LIB/names` is read as it is. So nothing is
# written while the questions are answered, and a refused fetch leaves
# BEND_LIB as it found it. It decides nothing; that it reads and executes
# faithfully is EZ-TRUST-2.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../lock/run.bend as Run
import ../lock/world.bend as W
import ../lock/up.bend as Up
import ./world.bend as FW
import ./plan.bend as FP

# a tree's manifest, when there is one: the tree as it names it, and
# otherwise a miss
def laid.seen(got: Maybe<&2, String>, +dir: String) -> IO(W.Answer):
  match got:
    case None{}:
      IO.pure(W.Answer, W.Miss{"ez: " ++ dir ++ " is not there"})
    case Some{text}:
      Run.answer.lib(dir, text)

# the tree under BEND_LIB for a hash, as its manifest names it, or a miss
# when there is none
def laid(+lib: String, +hash: String) -> IO(W.Answer):
  +dir = lib ++ "/" ++ hash
  do IO<W.Answer>:
    m : Maybe<&2, String> <- F.read(dir ++ "/manifest")
    laid.seen(m, dir)

# one question, answered
def answer(+lib: String, ask: FW.Ask) -> IO(FW.Answer):
  match ask:
    case FW.Laid{hash}:
      do IO<FW.Answer>:
        a : W.Answer <- laid(lib, hash)
        return FW.Read{a}
    case FW.Git{_hash, q}:
      do IO<FW.Answer>:
        a : Up.Answer <- Run.answer.up(lib, q)
        return FW.Said{a}
    case FW.Hub{q}:
      do IO<FW.Answer>:
        a : W.Answer <- Run.answer(lib, q)
        return FW.Read{a}
    case FW.Named{nv}:
      do IO<FW.Answer>:
        m : Maybe<&2, String> <- F.read(lib ++ "/names/" ++ nv)
        return FW.Held{m}

# every question, answered
def answer.all(+lib: String, asks: List<&2, FW.Ask>) -> IO(List<&2, FW.Reply>):
  match asks:
    case []:
      IO.pure(List<&2, FW.Reply>, [])
    case +h <> t:
      do IO<List<&2, FW.Reply>>:
        a : FW.Answer <- answer(lib, h)
        rest : List<&2, FW.Reply> <- answer.all(lib, t)
        return FW.Reply{h, a} <> rest

# the World with more answers in it
def more(world: FW.World, rs: List<&2, FW.Reply>) -> FW.World:
  FW.World{here, ledger, lock, replies} = world
  FW.World{here, ledger, lock, List.append(&2, FW.Reply, replies, rs)}

# the planner's step: its questions answered and the loop gone round again,
# or its plan run
def loop.step(st: FP.Step, +lib: String, world: FW.World, go: FW.World -> IO(Unit)) -> IO(Unit):
  match st:
    case FP.Asking{asks}:
      do IO<Unit>:
        rs : List<&2, FW.Reply> <- answer.all(lib, asks)
        go(more(world, rs))
    case FP.Run{pl}:
      Run.exec.plan(lib, pl)

# the loop, under fuel. A package asks at most twice, for its tree under
# BEND_LIB and for its fetch, and every round answers what it asked, so the
# fuel is only a guard.
def loop(fuel: Nat, +lib: String, +world: FW.World) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "ez: ez fetch kept asking questions")
    case 1n+f:
      loop.step(FP.step(world), lib, world, w => loop(f, lib, w))

# a file of the project, read
def at(+here: String, +file: String) -> String:
  here ++ "/" ++ file

# BEND_LIB `lib` filled from the lock of the project in `here`, which is
# where every relative path in the lock is read from. `ez tool` fills a
# tool's cache from its checkout's lock this way.
def fill(+here: String, +lib: String) -> IO(Unit):
  do IO<Unit>:
    led : Maybe<&2, String> <- F.read(at(here, FW.toml()))
    lk : Maybe<&2, String> <- F.read(at(here, FW.lockfile()))
    loop(U32.to_nat(10), lib, FW.World{here, Maybe.is_some(&2, String, led), lk, []})

# `ez fetch`: BEND_LIB filled from the lock of the project ez runs in
def run() -> IO(Unit):
  do IO<Unit>:
    lib : String <- Run.bend.lib()
    +pwd : String <- R.exec(["pwd"])
    fill(String.trim(R.text(pwd)), lib)

# tool/run: the interpreter for `ez tool run`, `install`, `upgrade` and
# `sync`. It reads the directory it runs in, the variables, the bend on the
# PATH, and the project's ez.toml and ez.lock.toml into a World, then loops:
# it asks the planner (tool/plan.bend) what is still open, answers each
# question by IO, and adds the answers to the World, until nothing is left
# to ask. Then it runs the plan: the checkout laid, the binary built or
# reused, then the program started or the link written, and the plan's end.
# A git question is the lock interpreter's to answer (`Run.answer.ups`), a
# file is written by its `Run.write`, and the end is its `Run.end`. It
# decides nothing; that it reads and executes faithfully is EZ-TRUST-2.
#
# `sync` asks the planner which pins to install (`TP.sync`) and installs
# each in turn as `ez tool install <name>` would.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../lock/run.bend as Run
import ../lock/up.bend as Up
import ../fetch/run.bend as FetchRun
import ../pkg/path.bend as P
import ../run/bend.bend as Bend
import ../ez/cap.bend as Cap
import ../ez/say.bend as Say
import ./world.bend as TW
import ./plan.bend as TP

# ---------------------------------------------------------------------------
# answering

# the first line, or nothing
def line0(ls: List<&2, String>) -> String:
  match ls:
    case []:
      ""
    case h <> _t:
      h

# what a git command printed, trimmed, or "" when it failed
def said(+out: String) -> String:
  Bool.pick(String, R.ok(out), String.trim(R.text(out)), "")

# what git says of a path that has a real path: the top of its checkout,
# HEAD, and what `git status` names, untracked files included whatever the
# repository's own settings hide
def located(+abs: String) -> IO(TW.Answer):
  do IO<TW.Answer>:
    +top : String <- R.exec(["git", "-C", abs, "rev-parse", "--show-toplevel"])
    +head : String <- R.exec(["git", "-C", abs, "rev-parse", "HEAD"])
    +st : String <- R.exec(["git", "-C", abs, "status", "--porcelain",
      "--untracked-files=normal"])
    return TW.Located{abs, said(top), said(head), R.ok(st), String.trim(R.text(st))}

# a path that has a real path, or why it has none
def locate.real(ok: Bool, +path: String, +text: String) -> IO(TW.Answer):
  match ok:
    case False{}:
      IO.pure(TW.Answer, TW.Miss{"ez: " ++ path ++ ": " ++ String.trim(text)})
    case True{}:
      located(String.trim(text))

# a local path, made real, and what git says of it
def locate(+path: String) -> IO(TW.Answer):
  do IO<TW.Answer>:
    +out : String <- R.exec(["realpath", path])
    locate.real(R.ok(out), path, R.text(out))

# one question answered
def answer(ask: TW.Ask) -> IO(TW.Answer):
  match ask:
    case TW.Read{path}:
      do IO<TW.Answer>:
        m : Maybe<&2, String> <- F.read(path)
        return TW.Text{m}
    case TW.Exec{path}:
      do IO<TW.Answer>:
        +out : String <- R.exec(["test", "-x", path])
        return TW.Is{R.ok(out)}
    case TW.Locate{path}:
      locate(path)

# every question answered
def answer.all(asks: List<&2, TW.Ask>) -> IO(List<&2, TW.Reply>):
  match asks:
    case []:
      IO.pure(List<&2, TW.Reply>, [])
    case +h <> t:
      do IO<List<&2, TW.Reply>>:
        a : TW.Answer <- answer(h)
        rest : List<&2, TW.Reply> <- answer.all(t)
        return TW.Reply{h, a} <> rest

# the World with more answers in it
def more(world: TW.World, rs: List<&2, TW.Reply>, us: List<&2, Up.Reply>) -> TW.World:
  TW.World{a, t, here, env, bend, ledger, lock, replies, ups} = world
  TW.World{a, t, here, env, bend, ledger, lock, List.append(&2, TW.Reply, replies, rs),
    List.append(&2, Up.Reply, ups, us)}

# ---------------------------------------------------------------------------
# executing

# a checkout laid: whatever was there removed, then every file, the record
# last
def exec.lay(layout: TP.Lay) -> IO(Unit):
  match layout:
    case TP.Still{}:
      IO.pure(Unit, Unit{})
    case TP.Lay{dir, ws}:
      do IO<Unit>:
        _rm : String <- R.exec(["rm", "-rf", dir])
        Run.exec.all("", ws)

# a build's output, kept when it failed
def compile.said(ok: Bool, +why: String, +text: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      do IO<Unit>:
        IO.write(why ++ text)
        IO.die(Unit, 1, "")

# `bend <file> -o <out>` under the memory cap, with the checkout's library
def compile(+lib: String, +file: String, +out: String) -> IO(Unit):
  do IO<Unit>:
    +on : Bool <- Cap.ok()
    Cap.warn(on)
    +g : String <- Cap.gb()
    _mk : String <- R.exec(["mkdir", "-p", P.dir(out)])
    +bin : String <- R.exec(Cap.argv(on, g, lib, ["bend", file, "-o", out]))
    compile.said(R.ok(bin), Cap.why(bin, g), R.text(bin))

# the binary: the checkout's lock fetched as `ez fetch` fetches one, with
# every relative path in it read from the checkout, the file built, the
# record written; or the one there reused
def exec.make(making: TP.Make) -> IO(Unit):
  match making:
    case TP.Skip{}:
      IO.pure(Unit, Unit{})
    case TP.Reuse{name}:
      IO.print_err(Say.reused(name))
    case TP.Make{top, +lib, file, out, at, key, +name}:
      do IO<Unit>:
        FetchRun.fill(top, lib)
        +s : Say.Spin <- Say.hold(Say.building(name))
        compile(lib, file, out)
        Say.done(s)
        Run.write(at, key)

# a status that parsed. Zero is success; anything else is that status.
def code.die(zero: Bool, status: U32) -> IO(Unit):
  match zero:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, status, "")

# the program's status, forwarded. A status that is not a number exits 1.
def code.of(exit: Maybe<&2, U32>) -> IO(Unit):
  match exit:
    case None{}:
      IO.die(Unit, 1, "")
    case Some{+n}:
      code.die(U32.is_eq(n, 0), n)

# the lines a person is told, each on stderr
def tell(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case []:
      IO.pure(Unit, Unit{})
    case h <> t:
      do IO<Unit>:
        IO.print_err(h)
        tell(t)

def link.after(ok: Bool, +at: String, +text: String, says: List<&2, String>) -> IO(Unit):
  match ok:
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ ": " ++ String.trim(text))
    case True{}:
      tell(says)

# the program started with its words, or the link written
def exec.finish(fin: TP.Finish) -> IO(Unit):
  match fin:
    case TP.Idle{}:
      IO.pure(Unit, Unit{})
    case TP.Launch{bin, args}:
      do IO<Unit>:
        +out : String <- R.exec(List.append(&2, String, [bin], args))
        IO.write(R.text(out))
        code.of(U32.read(R.code(out)))
    case TP.Link{bin, +dir, +name, says}:
      +at = dir ++ "/" ++ name
      do IO<Unit>:
        IO.print_err(Say.linking(at))
        _mk : String <- R.exec(["mkdir", "-p", dir])
        +ln : String <- R.exec(["ln", "-sfn", bin, at])
        link.after(R.ok(ln), at, R.text(ln), says)

# a plan, executed, and how it ends
def exec.plan(pl: TP.Plan) -> IO(Unit):
  TP.Plan{l, m, f, o} = pl
  do IO<Unit>:
    exec.lay(l)
    exec.make(m)
    exec.finish(f)
    Run.end(o)

# ---------------------------------------------------------------------------
# the loop

def loop.step(st: TP.Step, world: TW.World, go: TW.World -> IO(Unit)) -> IO(Unit):
  match st:
    case TP.Asking{asks, ups}:
      do IO<Unit>:
        rs : List<&2, TW.Reply> <- answer.all(asks)
        us : List<&2, Up.Reply> <- Run.answer.ups("", ups)
        go(more(world, rs, us))
    case TP.Run{pl}:
      exec.plan(pl)

# the loop, under fuel. Every round adds an answer, since the planner never
# asks what the World answers already, and it asks at most five rounds, so
# the fuel is only a guard.
def loop(fuel: Nat, +world: TW.World) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "ez: ez tool kept asking questions")
    case 1n+f:
      loop.step(TP.step(world), world, w => loop(f, w))

# a variable, "" when it is unset
def var(name: String) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env(name)
    return Run.env.text(r)

# the bend on the PATH, as its banner's first line. A bend that does not
# answer is "", and its build fails on its own.
def bend.is() -> IO(String):
  do IO<String>:
    +out : String <- Bend.version()
    return Bool.pick(String, R.ok(out), line0(String.lines(String.trim(R.text(out)))), "")

# the variables the tool commands read
def env() -> IO(TW.Env):
  do IO<TW.Env>:
    +b : String <- var("EZ_TOOL_BIN")
    +x : String <- var("XDG_BIN_HOME")
    +c : String <- var("XDG_CACHE_HOME")
    +h : String <- var("HOME")
    +p : String <- var("PATH")
    return TW.Env{b, x, c, h, p}

# one target, run, installed or upgraded, over the project's ledger and lock
def go(
  act: TW.Act,
  +target: String,
  +here: String,
  +vars: TW.Env,
  +bend: String,
  +led: Maybe<&2, String>,
  +lock: Maybe<&2, String>
) -> IO(Unit):
  loop(U32.to_nat(100), TW.World{act, target, here, vars, bend, led, lock, [], []})

# `ez tool run <target> [-- args…]`, `install` and `upgrade`
def run(act: TW.Act, +target: String) -> IO(Unit):
  do IO<Unit>:
    +pwd : String <- R.exec(["pwd"])
    +vars : TW.Env <- env()
    +bend : String <- bend.is()
    led : Maybe<&2, String> <- F.read("ez.toml")
    lock : Maybe<&2, String> <- F.read("ez.lock.toml")
    go(act, target, String.trim(R.text(pwd)), vars, bend, led, lock)

# every name a sync installs, in turn
def sync.all(
  ns: List<&2, String>,
  +here: String,
  +vars: TW.Env,
  +bend: String,
  +led: Maybe<&2, String>,
  +lock: Maybe<&2, String>
) -> IO(Unit):
  match ns:
    case []:
      IO.pure(Unit, Unit{})
    case +h <> t:
      do IO<Unit>:
        go(TW.Install{}, h, here, vars, bend, led, lock)
        sync.all(t, here, vars, bend, led, lock)

# a sync's names installed in turn, or its refusal
def sync.go(
  synced: TP.Sync,
  +here: String,
  +vars: TW.Env,
  +bend: String,
  +led: Maybe<&2, String>,
  +lock: Maybe<&2, String>
) -> IO(Unit):
  match synced:
    case TP.SyncNo{why}:
      IO.die(Unit, 1, why)
    case TP.Sync{ns}:
      sync.all(ns, here, vars, bend, led, lock)

# `ez tool sync`: every pin the ledger names, installed at its lock rev
def sync() -> IO(Unit):
  do IO<Unit>:
    +pwd : String <- R.exec(["pwd"])
    +vars : TW.Env <- env()
    +bend : String <- bend.is()
    +led : Maybe<&2, String> <- F.read("ez.toml")
    +lock : Maybe<&2, String> <- F.read("ez.lock.toml")
    sync.go(TP.sync(led, lock), String.trim(R.text(pwd)), vars, bend, led, lock)

# ez/cmd: what each subcommand does. Everything that touches the network or the
# file system goes through a process effect, because bend links no TLS and
# Base has neither mkdir nor readdir: snap's `exec` for a program whose answer
# ez reads, and `ez/pass.bend` for the one `ez run` hands the terminal to.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../lock/run.bend as Run
import ../lock/plan.bend as P
import ../ez/env.bend as Env
import ../ez/cap.bend as Cap
import ../ez/args.bend as Args
import ../ez/ends.bend as E
import ../ez/start.bend as S
import ../ez/pass.bend as Pass
import ../init/run.bend as InitRun
import ../remove/run.bend as RemoveRun
import ../add/run.bend as AddRun
import ../fetch/run.bend as FetchRun
import ../pub/run.bend as PubRun

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# what `ez check`, `ez build` or `ez run` does, decided from ez.toml as it is
# on disk (`S.start`): a missing or unreadable ledger is refused before
# anything is started or made
def started(+ask: S.Ask) -> IO(S.Start):
  do IO<S.Start>:
    t : Maybe<&2, String> <- F.read(toml())
    return S.start(ask, t)

# a refusal said, and the command ended on it with exit 1
def refused(+why: String) -> IO(Unit):
  Run.end(P.Refused{why})

# a build's output, printed with a word in front of it for a run the kernel
# ended rather than the program, and the command ended on it (`E.ran`): a
# failed build must fail the command, or a script around it learns nothing.
# bend prints that all terms check before it emits any C, so a build killed at
# the cap is otherwise indistinguishable from one that worked and wrote
# nothing.
def report.capped(+why: String, +out: String) -> IO(Unit):
  do IO<Unit>:
    IO.write(why ++ R.text(out))
    Run.end(E.ran(out))

# `ez check` and `ez run` are not capped, and `ez build` is. The wall
# `ez/cap.bend` exists for is bend's C backend: emitting the C for a large
# program peaked at 18.8 GB here and an uncapped one reached 35 GB. `ez check`
# emits JS and `ez run` interprets, so neither reaches that backend; and what
# `ez run` spends after that is the user's own program spending it, which is
# not ez's to ration.
#
# Whether a check passed is `E.check.passed`: bend exited 0, or said only
# that the entry has no main.

# a passing check says so, since bend says nothing when it is happy, and a
# failing one shows what bend said
def check.said(passed: Bool, entry: String, text: String) -> IO(Unit):
  match passed:
    case True{}:
      IO.print("ok " ++ entry)
    case False{}:
      IO.write(text)

# the entry checked, and never run, once `.ez` is there for its JS. The
# entry is the word after `bend` on the line.
def check.go(start: S.Start) -> IO(Unit):
  match start:
    case S.Refused{why}:
      refused(why)
    case S.Starts{+line}:
      do IO<Unit>:
        Env.make(Env.dirs("check", ""))
        +out : String <- Env.exec(line)
        check.said(E.check.passed(out), Args.at(line, 1n), R.text(out))
        Run.end(E.checked(out))

# `ez check`
def check() -> IO(Unit):
  do IO<Unit>:
    start : S.Start <- started(S.Check{})
    check.go(start)

# a native binary, named after the package (`S.build.out`), once the
# directory it lands in is there. This is the one command that reaches bend's
# C backend, so it is the one that runs under the memory cap.
def build.go(start: S.Start, +out: String) -> IO(Unit):
  match start:
    case S.Refused{why}:
      refused(why)
    case S.Starts{line}:
      do IO<Unit>:
        Env.make(Env.dirs("build", out))
        +cap : Bool <- Cap.ok()
        Cap.warn(cap)
        +g : String <- Cap.gb()
        +bin : String <- Cap.run(cap, line)
        report.capped(Cap.why(bin, g), bin)

# `ez build [out]`
def build(+out: String) -> IO(Unit):
  do IO<Unit>:
    start : S.Start <- started(S.Build{out})
    build.go(start, out)

# the program `ez run` starts, on ez's own stdin, stdout and stderr, with the
# project's BEND_LIB set for it, and the status it exited with; 0 when the
# run was refused, which starts none
def run.started(start: S.Start, +at: String) -> IO(U32):
  match start:
    case S.Refused{_why}:
      IO.pure(U32, 0)
    case S.Starts{line}:
      Pass.run(Env.line(at, line))

# a run, and how it ends: exit 1 with the reason for a refusal, and the
# program's own status otherwise (`S.code`, EZ-OUT-1)
def run.go(+start: S.Start) -> IO(Unit):
  do IO<Unit>:
    at : String <- Env.lib()
    +program : U32 <- run.started(start, at)
    +code : U32 <- IO.pure(U32, S.code(start, program))
    Run.end.at(U32.is_eq(code, 0), code, S.why(start))

# `ez run [args..]`: the entry run by bend, which checks it first, with every
# word after `run`, as `cargo run` runs a project's binary
def run(as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +start : S.Start <- started(S.Run{as})
    run.go(start)

# `ez publish`, planned by pub/plan.bend: the entry the ledger names, sent to
# the hub once the tree is clean and git tracks every file of the package,
# and bend's answer checked against the `0x` name ez computed. A ledger that
# is missing or does not parse is refused, and nothing is sent.
def publish() -> IO(Unit):
  PubRun.run()

# `ez lock`, plain or `--upgrade`, is the planner's
# (lock/plan.bend, lock/up.bend): a plain lock copies every pin as the ledger
# has it, refuses one it would have to fill, and never writes ez.toml; an
# upgrade moves the selected pins, writes ez.toml once, `.gitignore`, the
# rewritten imports and the lock in one plan. Either writes nothing when it
# refuses, and a missing ledger is refused. `--package` is only a filter on an
# upgrade.
# `--package` without `--upgrade` is refused before anything is read
# (`E.lock.flags`).
def lock.go(flags: P.Outcome, up: Bool, +name: String) -> IO(Unit):
  match flags:
    case P.Success{}:
      Run.run(up, name)
    case P.Refused{why}:
      Run.end(P.Refused{why})

# `ez lock` and `ez lock --upgrade [--package NAME]`
def lock(+up: Bool, +name: String) -> IO(Unit):
  lock.go(E.lock.flags(up, name), up, name)

# `ez fetch`, planned by fetch/plan.bend: BEND_LIB filled from the lock, with
# nothing re-resolved, and nothing laid unless every package checks
def fetch() -> IO(Unit):
  FetchRun.run()

# `ez init [name] [entry.bend] [--description TEXT]`: a new project, planned
# by init/plan.bend
def init(+asked: String, +file: String, +desc: String) -> IO(Unit):
  InitRun.run(asked, file, desc)

# `ez add <target> [rev|tag|branch] [entry.bend] [--rename NAME]`, planned by
# add/plan.bend. The target is an `owner/repo`, a git url, or a path, the same
# shapes `ez tool run` takes, or a hub package's `<name>@<version>`
# (add/hub.bend). A missing ref is resolved, and a missing entry is read from
# the checkout, or from the package the hub serves.
def add(+target: String, +ref: String, +entry: String, +rename: String) -> IO(Unit):
  AddRun.run(target, ref, entry, rename)

# `ez remove <name>`, planned by remove/plan.bend
def remove(+name: String) -> IO(Unit):
  RemoveRun.run(name)

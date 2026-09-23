# ez/cmd: what each subcommand does. Everything that touches the network or the
# file system goes through one process effect, because bend links no TLS and
# Base has neither mkdir nor readdir.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../manifest/manifest.bend as M
import ../lock/run.bend as Run
import ../lock/world.bend as W
import ../pub/pub.bend as Pub
import ../ez/env.bend as Env
import ../ez/cap.bend as Cap
import ../ez/args.bend as Args
import ../init/run.bend as InitRun
import ../remove/run.bend as RemoveRun
import ../add/run.bend as AddRun
import ../fetch/run.bend as FetchRun

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# the ledger on disk, parsed
def load() -> IO(M.Read):
  do IO<M.Read>:
    t : Maybe<&2, String> <- F.read(toml())
    return M.parse(F.text_of(t))

# a failed run must fail the command, or a script around it learns nothing
def report.exit(ok: Bool) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "")

# a run's output, printed, and its status turned into this program's
def report(+out: String) -> IO(Unit):
  do IO<Unit>:
    IO.write(R.text(out))
    report.exit(R.ok(out))

# the same, with a word in front of it for a run the kernel ended rather than
# the program. bend prints that all terms check before it emits any C, so a
# build killed at the cap is otherwise indistinguishable from one that worked
# and wrote nothing.
def report.capped(+why: String, +out: String) -> IO(Unit):
  do IO<Unit>:
    IO.write(why ++ R.text(out))
    report.exit(R.ok(out))

# the entry file a ledger names, or "main.bend" when it names none
def entry.or(+file: String) -> String:
  Bool.pick(String, String.is_empty(file), "main.bend", file)

# the name a ledger gives the package, or `app` when there is no ledger to ask
def named(ledger: M.Read) -> String:
  match ledger:
    case M.Bad{_why}:
      "app"
    case M.Good{m}:
      M.Manifest{n, _e, _b, _h, _ds, _ts} = m
      n

# the entry file of a ledger that was read
def entry(ledger: M.Read) -> String:
  match ledger:
    case M.Bad{_why}:
      "main.bend"
    case M.Good{m}:
      M.Manifest{_n, e, _b, _h, _ds, _ts} = m
      entry.or(e)

# a ledger that would not parse stops the command before it does damage
def refuse(ledger: M.Read) -> IO(Unit):
  IO.die(Unit, 1, "ez: " ++ M.show(ledger))

# `ez check` and `ez run` are not capped, and `ez build` is. The wall
# `ez/cap.bend` exists for is bend's C backend: emitting the C for a large
# program peaked at 18.8 GB here and an uncapped one reached 35 GB. `ez check`
# emits JS and `ez run` interprets, so neither reaches that backend; and what
# `ez run` spends after that is the user's own program spending it, which is
# not ez's to ration.
#
# `bend f -o out` checks without running main. A clean file prints nothing at
# all, and a library entry, having no main, checks clean and then exits 1 with
# "no main to run" from the emit. A check failure throws before the emit, so
# that message can only follow a check that passed.
#
# It is matched as a whole line, because that is the shape of the thing being
# claimed: bend prints it as `Error: no main to run` and nothing else. Asked as
# a substring of the whole output, the same words appearing anywhere — inside
# some other error's text, or in a source line bend echoed back while
# reporting on it — would answer yes and mean nothing, and a failing check
# would read as a passing one. Two other line-shaped facts in this tree were
# being asked of whole files the same way, and one of them silently dropped a
# test before it was caught.
def no.main(+line: String) -> Bool:
  String.eq(line, "Error: no main to run")

# whether any line of the output is that one. The rest of the walk is bound
# before the `Bool.or` rather than written under it: `Bool.or` is an ordinary
# function and reduces both sides, so a recursive call sitting inside one is
# not a branch the condition can decline. Bound first it is a plain fold over
# a handful of lines, which is what the rest of this tree does too.
def said.no.main(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case Con{+h, t}:
      +rest = said.no.main(t)
      Bool.or(no.main(h), rest)

def check.passed(+out: String) -> Bool:
  Bool.or(R.ok(out), said.no.main(String.lines(R.text(out))))

# a passing check says so, since bend says nothing when it is happy
def check.said(passed: Bool, entry: String, text: String) -> IO(Unit):
  match passed:
    case True{}:
      IO.print("ok " ++ entry)
    case False{}:
      do IO<Unit>:
        IO.write(text)
        IO.die(Unit, 1, "")

# the entry checked, and never run
def check() -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load()
    +at : String <- IO.pure(String, entry(r))
    +out : String <- Env.exec(["bend", at, "-o", ".ez/check.js"])
    check.said(check.passed(out), at, R.text(out))

# where a build lands when nothing said: `bin/<package name>.out`. The name
# and not the entry file, because the entry is where a program starts and the
# name is what it is called — a package named `bolt` with its entry at
# `bolt/main.bend` builds `bin/bolt.out` and not `bin/main.out`.
def build.named(+name: String) -> String:
  "bin/" ++ name ++ ".out"

# where a build lands: what was asked for, or the default
def build.out(+at: String, +name: String) -> String:
  Bool.pick(String, String.is_empty(at), build.named(name), at)

# a native binary, named after the package. This is the one command that
# reaches bend's C backend, so it is the one that runs under the memory cap.
def build(+out: String) -> IO(Unit):
  do IO<Unit>:
    +r : M.Read <- load()
    +cap : Bool <- Cap.ok()
    Cap.warn(cap)
    +g : String <- Cap.gb()
    +bin : String <- Cap.run(cap, ["bend", entry(r), "-o",
      build.out(out, named(r))])
    report.capped(Cap.why(bin, g), bin)

# the entry run, which checks it first, with every word after `run`
def run(as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load()
    +out : String <- Env.exec(Args.run.line(entry(r), as))
    report(out)

# `ez publish`: the entry the ledger names, sent to the hub the way `ez build`
# and `ez check` build and check that same entry. The `0x` name reported is the
# one `pkg/pkg.bend` computed from the file set; what `bend --publish` printed
# is only checked against it. `pub/pub.bend` holds the whole of it, laws and
# all, and is handed the project's BEND_LIB the way `git/git.bend` is handed it
# for a vendoring.
def publish() -> IO(Unit):
  do IO<Unit>:
    r : M.Read <- load()
    +at : String <- IO.pure(String, entry(r))
    lib : String <- Env.lib()
    Pub.publish(lib, at)

# `ez lock`, plain or `--upgrade`, is the planner's
# (lock/plan.bend, lock/up.bend): a plain lock copies every pin as the ledger
# has it, refuses one it would have to fill, and never writes ez.toml; an
# upgrade moves the selected pins, writes ez.toml once, `.gitignore`, the
# rewritten imports and the lock in one plan. Either writes nothing when it
# refuses, and a missing ledger is refused. `--package` is only a filter on an
# upgrade.
def lock.go(ok: Bool, up: Bool, +name: String) -> IO(Unit):
  match ok:
    case True{}:
      Run.run(up, name)
    case False{}:
      IO.die(Unit, 1, "ez: --package needs --upgrade")

# `ez lock` and `ez lock --upgrade [--package NAME]`
def lock(+up: Bool, +name: String) -> IO(Unit):
  lock.go(Bool.or(up, String.is_empty(name)), up, name)

# `ez fetch`, planned by fetch/plan.bend: BEND_LIB filled from the lock, with
# nothing re-resolved, and nothing laid unless every package checks
def fetch() -> IO(Unit):
  FetchRun.run()

# `ez init [name] [entry.bend]`: a new project, planned by init/plan.bend
def init(+asked: String, +file: String) -> IO(Unit):
  InitRun.run(asked, file)

# `ez add <target> [rev|tag|branch] [entry.bend] [--rename NAME]`, planned by
# add/plan.bend. The target is an `owner/repo`, a git url, or a path, the same
# shapes `ez tool run` takes. A missing ref is resolved, and a missing entry
# is read from the checkout.
def add(+target: String, +ref: String, +entry: String, +rename: String) -> IO(Unit):
  AddRun.run(target, ref, entry, rename)

# `ez remove <name>`, planned by remove/plan.bend
def remove(+name: String) -> IO(Unit):
  RemoveRun.run(name)

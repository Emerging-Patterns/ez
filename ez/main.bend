# ez: the one binary. The line is a Shake.Cli (`L.spec`): `parse` binds the
# command and its flags, and `get` / `on` read the bindings. How a line ends
# is decided in ez/line.bend (`L.line`, `L.status`): a command runs, help is
# shown and the line exits 0, or the line is misused and exits 1. This file
# prints and exits as they say and runs the command, which is trusted under
# EZ-TRUST-2. `IO.args()` is copied so each word can be read more than once.
# Build it
# native (`bend ez/main.bend -o bin/ez.bin`); interpreted, bend's own CLI
# would take the flags meant for ez.
import Base
import 0xebdf72b20ad527103f6efc0d2aa8f1ec/main.bend as Shake
import ../ez/args.bend as Args
import ./cmd.bend as Cmd
import ./test.bend as Test
import ./prove.bend as Prove
import ../doctor/run.bend as DoctorRun
import ../tool/run.bend as ToolRun
import ../tool/world.bend as TW
import ../ez/say.bend as Say
import ../io/file.bend as F
import ../ez/line.bend as L

# what a subcommand runs. `L.line` never runs `CHelp`, which names no
# command; it is here so the match is whole, and it writes the help a bare
# `ez` would. The directories `ez check` and `ez build` write into are made
# by those commands once they know they will start bend (`Env.dirs`), so a
# refused one leaves the directory as it found it.
def dispatch(sub: L.Sub, +matched: Shake.Matched, +as: List<&2, String>) -> IO(Unit):
  match sub:
    case L.CInit{}:
      Cmd.init(Shake.get(matched, "name"), Shake.get(matched, "entry"),
        Shake.get(matched, "description"))
    case L.CAdd{}:
      Cmd.add(Shake.get(matched, "target"), Shake.get(matched, "ref"),
        Shake.get(matched, "entry"), Shake.get(matched, "rename"))
    case L.CRemove{}:
      Cmd.remove(Shake.get(matched, "name"))
    case L.CLock{}:
      Cmd.lock(Shake.on(matched, "upgrade"), Shake.get(matched, "package"))
    case L.CFetch{}:
      Cmd.fetch()
    case L.CCheck{}:
      Cmd.check()
    case L.CBuild{}:
      Cmd.build(Shake.get(matched, "out"))
    case L.CRun{}:
      Cmd.run(as)
    case L.CToolSync{}:
      ToolRun.sync()
    case L.CToolRun{}:
      ToolRun.run(TW.Run{Args.tool.rest(as)}, Shake.get(matched, "target"),
        Shake.get(matched, "entry"))
    case L.CToolInstall{}:
      ToolRun.run(TW.Install{}, Shake.get(matched, "target"), Shake.get(matched, "entry"))
    case L.CToolUpgrade{}:
      ToolRun.run(TW.Upgrade{}, Shake.get(matched, "target"), Shake.get(matched, "entry"))
    case L.CPublish{}:
      Cmd.publish()
    case L.CTest{}:
      Test.run()
    case L.CProve{}:
      Prove.run()
    case L.CDoctor{}:
      DoctorRun.run()
    case L.CHelp{}:
      IO.write(Shake.help(L.spec(), []))

# `sync` with no tools is lock or install; a ledger that pins tools already
# names the command that builds them. Anything else is the parser's own error.
def hint.sync(is_sync: Bool) -> IO(Unit):
  match is_sync:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        m : Maybe<&2, String> <- F.read("ez.toml")
        IO.print_err(Say.hint(Say.has.tools(F.text_of(m))))

# what a line says: the command it names run, its help on stdout, or what
# was wrong with it on stderr, with a hint for `ez sync`
def go.say(how: L.Line, +as: List<&2, String>) -> IO(Unit):
  match how:
    case L.Runs{sub, +m}:
      dispatch(sub, m, as)
    case L.Shows{text}:
      IO.write(text)
    case L.Misuse{text, word}:
      do IO<Unit>:
        IO.print_err(text)
        hint.sync(String.eq(word, "sync"))

# a status that is 0 ends nothing, and any other exits with it
def go.exit(zero: Bool, +code: U32) -> IO(Unit):
  match zero:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, code, "")

# a status decided before any command ran, exited with; a command's own end
# is its own
def go.end(st: L.Status) -> IO(Unit):
  match st:
    case L.Exits{+code}:
      go.exit(U32.is_eq(code, 0), code)
    case L.Ends{}:
      IO.pure(Unit, Unit{})

# how the line ends, as `L.line` decided, and the status `L.status` gives it
def go.line(+how: L.Line, +as: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    go.say(how, as)
    go.end(L.status(how))

# the line taken apart
def go(+app: Shake.Cli, +as: List<&2, String>) -> IO(Unit):
  go.line(L.line(app, Shake.parse(app, Args.argv.of(as))), as)

def main() -> IO(Unit):
  do IO<Unit>:
    as : List<&2, String> <- Args.all()
    go(L.spec(), as)

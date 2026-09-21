# ez: the one binary. The line is a Shake.Cli: `parse` binds the command
# and its flags, `help` writes usage, and `get` / `on` read the bindings.
# `IO.args()` is copied so each word can be read more than once. Build it
# native (`bend ez/main.bend -o bin/ez.bin`); interpreted, bend's own CLI
# would take the flags meant for ez.
import Base
import 0xebdf72b20ad527103f6efc0d2aa8f1ec/main.bend as Shake
import ./args.bend as Args
import ./cmd.bend as Cmd
import ./test.bend as Test
import ./doctor.bend as Doctor
import ./env.bend as Env

# a subcommand
type Sub is Data:
  CInit{}
  CAdd{}
  CRemove{}
  CLock{}
  CFetch{}
  CCheck{}
  CBuild{}
  CRun{}
  CPublish{}
  CTest{}
  CDoctor{}
  CHelp{}

# the program: every command, and the flags and positionals it binds
def spec() -> Shake.Cli:
  Shake.app("ez", "dependency tracking and builds for Bend 2", None{},
    [],
    [
      Shake.sub("init", "scaffold a project: ez.toml, ignore, entry",
        [
          Shake.pos("name", "package name", False{}, None{}, []),
          Shake.pos("entry", "entry file", False{}, None{}, [])
        ], []),
      Shake.sub("add", "vendor a git package and record it",
        [
          Shake.pos("url", "git url", True{}, None{}, []),
          Shake.pos("ref", "commit, tag or branch", True{}, None{}, []),
          Shake.pos("entry", "entry file", True{}, None{}, [])
        ], []),
      Shake.sub("remove", "drop a package from the ledger",
        [
          Shake.pos("name", "package name", True{}, None{}, [])
        ], []),
      Shake.sub("lock", "resolve every import, write ez.lock.toml", [], []),
      Shake.sub("fetch", "fill BEND_LIB from the lock", [], []),
      Shake.sub("check", "check the entry, without running it", [], []),
      Shake.sub("build", "build the entry to a native binary",
        [
          Shake.pos("out", "output path", False{}, None{}, [])
        ], []),
      Shake.sub("run", "check and run the entry", [], []),
      Shake.sub("publish", "send the entry to the hub, under ez's 0x name",
        [], []),
      Shake.sub("test", "run every */tests/*.bend, on both lanes",
        [
          Shake.flag("js-only", None{}, Some{"js-only"},
            "run the JS lane only"),
          Shake.flag("full", None{}, Some{"full"}, "ignore the cache"),
          Shake.flag("unit-only", None{}, Some{"unit-only"},
            "skip the end-to-end tests")
        ], []),
      Shake.sub("doctor", "report on the toolchain and the project", [], [])
    ])

# a subcommand by its name
def command(+name: String) -> Sub:
  Bool.pick(Sub, String.eq(name, "init"), CInit{},
    Bool.pick(Sub, String.eq(name, "add"), CAdd{},
      Bool.pick(Sub, String.eq(name, "remove"), CRemove{},
        Bool.pick(Sub, String.eq(name, "lock"), CLock{},
          Bool.pick(Sub, String.eq(name, "fetch"), CFetch{},
            Bool.pick(Sub, String.eq(name, "check"), CCheck{},
              Bool.pick(Sub, String.eq(name, "build"), CBuild{},
                Bool.pick(Sub, String.eq(name, "run"), CRun{},
                  Bool.pick(Sub, String.eq(name, "publish"), CPublish{},
                    Bool.pick(Sub, String.eq(name, "test"), CTest{},
                      Bool.pick(Sub, String.eq(name, "doctor"), CDoctor{},
                        CHelp{})))))))))))

# what a subcommand runs
def dispatch(sub: Sub, +m: Shake.Matched, as: List<&2, String>) -> IO(Unit):
  match sub:
    case CInit{}:
      Cmd.init(Shake.get(m, "name"), Shake.get(m, "entry"))
    case CAdd{}:
      Cmd.add(Shake.get(m, "url"), Shake.get(m, "ref"), Shake.get(m, "entry"))
    case CRemove{}:
      Cmd.remove(Shake.get(m, "name"))
    case CLock{}:
      Cmd.lock()
    case CFetch{}:
      Cmd.fetch()
    case CCheck{}:
      Cmd.check()
    case CBuild{}:
      Cmd.build(Shake.get(m, "out"))
    case CRun{}:
      Cmd.run(as)
    case CPublish{}:
      Cmd.publish()
    case CTest{}:
      Test.run(Shake.on(m, "js-only"), Shake.on(m, "full"),
        Shake.on(m, "unit-only"))
    case CDoctor{}:
      Doctor.run()
    case CHelp{}:
      IO.write(Shake.help(spec(), []))

# a hard error
def fail.err(+app: Shake.Cli, e: Shake.ParseErr) -> IO(Unit):
  do IO<Unit>:
    IO.print_err(Shake.err_text(app, e))
    IO.die(Unit, 1, "")

# a failed parse: help text, or an error
def fail(+app: Shake.Cli, e: Shake.ParseErr) -> IO(Unit):
  match e:
    case Shake.NeedHelp{path}:
      IO.write(Shake.help(app, path))
    case other:
      fail.err(app, other)

# a successful parse: the command named by the path, then its bindings
def go.done(+as: List<&2, String>, +m: Shake.Matched) -> IO(Unit):
  dispatch(command(String.join(Shake.path_of(m), "/")), m, Args.rest(as))

# the parse result
def go.parsed(+app: Shake.Cli, +as: List<&2, String>,
  r: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> IO(Unit):
  match r:
    case Fail{e}:
      fail(app, e)
    case Done{m}:
      go.done(as, m)

# the line taken apart
def go(+app: Shake.Cli, +as: List<&2, String>) -> IO(Unit):
  go.parsed(app, as, Shake.parse(app, Args.argv.of(as)))

def main() -> IO(Unit):
  do IO<Unit>:
    Env.make()
    as : List<&2, String> <- Args.all()
    go(spec(), as)

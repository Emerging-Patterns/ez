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
import ./prove.bend as Prove
import ./doctor.bend as Doctor
import ./env.bend as Env
import ./tool.bend as Tool
import ../ez/say.bend as Say
import ../io/file.bend as F

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
  CProve{}
  CDoctor{}
  CToolSync{}
  CToolRun{}
  CToolInstall{}
  CToolUpgrade{}
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
          Shake.pos("target", "owner/repo, git url, or path", True{}, None{},
            []),
          Shake.pos("ref", "commit, tag or branch", False{}, None{}, []),
          Shake.pos("entry", "entry file", False{}, None{}, [])
        ], []),
      Shake.sub("remove", "drop a package from the ledger",
        [
          Shake.pos("name", "package name", True{}, None{}, [])
        ], []),
      Shake.sub("lock", "resolve every import, write ez.lock.toml",
        [
          Shake.flag("upgrade", None{}, Some{"upgrade"},
            "re-pin git deps and tools that moved, then write the lock"),
          Shake.opt("package", None{}, Some{"package"},
            "with --upgrade, only this dependency or tool", False{}, None{}, [])
        ], []),
      Shake.sub("fetch", "fill BEND_LIB from the lock", [], []),
      Shake.sub("check", "check the entry, without running it", [], []),
      Shake.sub("build", "build the entry to a native binary",
        [
          Shake.pos("out", "output path", False{}, None{}, [])
        ], []),
      Shake.sub("run", "check and run the entry", [], []),
      Shake.sub("tool", "build or run another project's binary", [], [
        Shake.sub("sync", "build and link every pinned tool at its lock rev",
          [], []),
        Shake.sub("run", "fetch, build and run the binary a repo declares",
          [
            Shake.pos("target", "owner/repo, git url, or path", True{}, None{},
              [])
          ], []),
        Shake.sub("install", "build the binary and link it on PATH",
          [
            Shake.pos("target", "owner/repo, git url, or path", True{}, None{},
              [])
          ], []),
        Shake.sub("upgrade", "rebuild when the commit moved, and refresh the link",
          [
            Shake.pos("target", "owner/repo, git url, or path", True{}, None{},
              [])
          ], [])
      ]),
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
      Shake.sub("prove", "check every PROOF.bend: the proof gate", [], []),
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
                      Bool.pick(Sub, String.eq(name, "prove"), CProve{},
                        Bool.pick(Sub, String.eq(name, "doctor"), CDoctor{},
                          Bool.pick(Sub, String.eq(name, "tool/sync"), CToolSync{},
                            Bool.pick(Sub, String.eq(name, "tool/run"), CToolRun{},
                              Bool.pick(Sub, String.eq(name, "tool/install"),
                                CToolInstall{},
                                Bool.pick(Sub, String.eq(name, "tool/upgrade"),
                                  CToolUpgrade{},
                                  CHelp{}))))))))))))))))

# what a subcommand runs
def dispatch(sub: Sub, +matched: Shake.Matched, +as: List<&2, String>) -> IO(Unit):
  match sub:
    case CInit{}:
      Cmd.init(Shake.get(matched, "name"), Shake.get(matched, "entry"))
    case CAdd{}:
      Cmd.add(Shake.get(matched, "target"), Shake.get(matched, "ref"),
        Shake.get(matched, "entry"))
    case CRemove{}:
      Cmd.remove(Shake.get(matched, "name"))
    case CLock{}:
      Cmd.lock(Shake.on(matched, "upgrade"), Shake.get(matched, "package"))
    case CFetch{}:
      Cmd.fetch()
    case CCheck{}:
      Cmd.check()
    case CBuild{}:
      Cmd.build(Shake.get(matched, "out"))
    case CRun{}:
      Cmd.run(Args.rest(as))
    case CToolSync{}:
      Tool.sync()
    case CToolRun{}:
      Tool.run(Shake.get(matched, "target"), Args.tool.rest(as))
    case CToolInstall{}:
      Tool.install(Shake.get(matched, "target"))
    case CToolUpgrade{}:
      Tool.upgrade(Shake.get(matched, "target"))
    case CPublish{}:
      Cmd.publish()
    case CTest{}:
      Test.run(Shake.on(matched, "js-only"), Shake.on(matched, "full"),
        Shake.on(matched, "unit-only"))
    case CProve{}:
      Prove.run()
    case CDoctor{}:
      Doctor.run()
    case CHelp{}:
      IO.write(Shake.help(spec(), []))

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

def hint.of(err: Shake.ParseErr) -> IO(Unit):
  match err:
    case Shake.Unexpected{arg}:
      hint.sync(String.eq(arg, "sync"))
    case Shake.UnknownFlag{_word}:
      IO.pure(Unit, Unit{})
    case Shake.Missing{_name}:
      IO.pure(Unit, Unit{})
    case Shake.BadValue{_name, _value}:
      IO.pure(Unit, Unit{})
    case Shake.NeedHelp{_path}:
      IO.pure(Unit, Unit{})

# a hard error
def fail.err(+app: Shake.Cli, +problem: Shake.ParseErr) -> IO(Unit):
  do IO<Unit>:
    IO.print_err(Shake.err_text(app, problem))
    hint.of(problem)
    IO.die(Unit, 1, "")

# a failed parse: help text, or an error
def fail(+app: Shake.Cli, err: Shake.ParseErr) -> IO(Unit):
  match err:
    case Shake.NeedHelp{path}:
      IO.write(Shake.help(app, path))
    case other:
      fail.err(app, other)

# a successful parse: the command named by the path, then its bindings
def go.done(+as: List<&2, String>, +matched: Shake.Matched) -> IO(Unit):
  dispatch(command(String.join(Shake.path_of(matched), "/")), matched, as)

# the parse result
def go.parsed(
  +app: Shake.Cli,
  +as: List<&2, String>,
  parsed: Result<&2, &2, Shake.ParseErr, Shake.Matched>
) -> IO(Unit):
  match parsed:
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

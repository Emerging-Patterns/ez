# ez/line: the command line, taken apart before any command runs. `spec` is
# the program, `command` names what a matched path runs, and `line` decides
# how a parse ends: a command runs, help is shown, or the line is misused.
# All of it is pure, so the status a line exits with before any command runs
# is a law (EZ-OUT-1); ez/main.bend prints and exits as `line` and `status`
# say, and runs the command a line names, whose own end decides the rest.
import Base
import 0x085b03c84ca37125e38dddede7b91e55/main.bend as Shake

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
      Shake.sub("init", "scaffold a project: ez.toml, ignore, entry, src/",
        [
          Shake.pos("name", "package name", False{}, None{}, []),
          Shake.pos("entry", "entry file", False{}, None{}, []),
          Shake.opt("description", None{}, Some{"description"},
            "one line: the entry's first line, which the hub shows", False{}, None{}, [])
        ], []),
      Shake.sub("add", "record a git or hub package",
        [
          Shake.pos("target", "owner/repo, git url, path, or name@version", True{}, None{},
            []),
          Shake.pos("ref", "commit, tag or branch", False{}, None{}, []),
          Shake.pos("entry", "entry file", False{}, None{}, []),
          Shake.opt("rename", None{}, Some{"rename"},
            "record it under this name, ahead of its own (a TOML bare key)",
            False{}, None{}, [])
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
            Shake.pos("target", "owner/repo, git url, path, or name@version", True{}, None{},
              []),
            Shake.opt("entry", None{}, Some{"entry"},
              "build this file of the checkout, not the one it names", False{}, None{}, [])
          ], []),
        Shake.sub("install", "build the binary and link it on PATH",
          [
            Shake.pos("target", "owner/repo, git url, path, or name@version", True{}, None{},
              []),
            Shake.opt("entry", None{}, Some{"entry"},
              "build this file of the checkout, not the one it names", False{}, None{}, [])
          ], []),
        Shake.sub("upgrade", "rebuild when the commit moved, and refresh the link",
          [
            Shake.pos("target", "owner/repo, git url, path, or name@version", True{}, None{},
              []),
            Shake.opt("entry", None{}, Some{"entry"},
              "build this file of the checkout, not the one it names", False{}, None{}, [])
          ], [])
      ]),
      Shake.sub("publish", "send the entry to the hub, under ez's 0x name",
        [], []),
      Shake.sub("test", "run every */tests/*.bend against its trailer", [], []),
      Shake.sub("prove", "check every PROOF.bend: the proof gate",
        [], []),
      Shake.sub("doctor", "report on the toolchain and the project", [], [])
    ])

# a subcommand by its path, the words joined with `/`. A path that names no
# command, the empty one of a bare `ez` or a group such as `tool`, is `CHelp`.
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

# whether a subcommand is the one that names no command
def is.help(sub: Sub) -> Bool:
  match sub:
    case CHelp{}:
      True{}
    case _:
      False{}

# the path a match names, its words joined with `/`
def path(matched: Shake.Matched) -> String:
  String.join(Shake.path_of(matched), "/")

# the Matched of the command the path names, whose bindings are the ones the
# line made for that command (SHAKE-GET-2: `at(m, path_of(m))` follows the
# selected path). A None here would be a Matched `parse` never answers.
def leaf(+matched: Shake.Matched) -> Shake.Matched:
  Maybe.default(&2, Shake.Matched, Shake.at(matched, Shake.path_of(matched)), matched)

# the value the command bound to `name`, or "" when it bound none
def get(found: Shake.Matched, +name: String) -> String:
  Maybe.default(&2, String, Shake.get(found, name), "")

# ---------------------------------------------------------------------------
# how a line ends

# a command runs, with what the line bound for it; help is shown, on stdout;
# or the line is misused, and says so on stderr
type Line is Data:
  Runs{sub: Sub, matched: Shake.Matched}
  Shows{text: String}
  Misuse{text: String}

# a line Shake would not parse: a request for help, whose path Shake has
# already checked word by word (SHAKE-PARSE-8: `help bogus` fails as
# `Unexpected`, not as a request for help), or a usage error
def line.err(help: Maybe<&2, List<&2, String>>, +app: Shake.Cli, err: Shake.ParseErr) -> Line:
  match help:
    case Some{path}:
      Shows{Shake.help(app, path)}
    case None{}:
      Misuse{Shake.err_text(app, err)}

# a path that names no command: a bare `ez` is help, as a bare `cargo` is,
# and a bare group such as `ez tool` is a line that did not say which of its
# commands to run, as `cargo report` with no command is, so its help goes to
# stderr and the line fails
def line.group(bare: Bool, +app: Shake.Cli, +matched: Shake.Matched) -> Line:
  match bare:
    case True{}:
      Shows{Shake.help(app, [])}
    case False{}:
      Misuse{Shake.help(app, Shake.path_of(matched))}

# a line Shake parsed: the command its path names runs, or it names none
def line.run(help: Bool, sub: Sub, +app: Shake.Cli, +matched: Shake.Matched) -> Line:
  match help:
    case True{}:
      line.group(String.is_empty(path(matched)), app, matched)
    case False{}:
      Runs{sub, leaf(matched)}

# how a line ends, from what Shake made of it
def line(+app: Shake.Cli, parsed: Result<&2, &2, Shake.ParseErr, Shake.Matched>) -> Line:
  match parsed:
    case Fail{+e}:
      line.err(Shake.help_path(e), app, e)
    case Done{+m}:
      +sub = command(path(m))
      line.run(is.help(sub), sub, app, m)

# ---------------------------------------------------------------------------
# the status

# the status a line exits with, when it is decided here, or the command's
# own end (EZ-OUT-1)
type Status is Data:
  Exits{code: U32}
  Ends{}

# help exits 0, a misused line 1, and a command that runs ends as it ends
def status(how: Line) -> Status:
  match how:
    case Runs{_sub, _m}:
      Ends{}
    case Shows{_text}:
      Exits{0}
    case Misuse{_text}:
      Exits{1}

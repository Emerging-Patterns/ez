# ez/env: the environment ez hands to the programs it runs. Vendored packages
# live with the project rather than in ~/.bend/lib, so every `bend` ez starts
# has to be told where they are. Base has `get_env` and no `set_env`, and the
# one foreign effect execvp's what it is given, so the variable rides in front
# of the command as `env BEND_LIB=... bend ...`. `env` is coreutils and is
# execvp'd like any other program, so no shell is involved.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ./args.bend as Args

# a value, or the fallback when the variable was unset or empty
def or_else(+value: String, +alt: String) -> String:
  Bool.pick(String, String.is_empty(value), alt, value)

# what a variable holds, with a default for when it holds nothing
def var(name: String, +alt: String) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env(name)
    return or_else(Args.text_of(r), alt)

# where this project's packages live
def lib() -> IO(String):
  var("BEND_LIB", ".ez/lib")

# the command with the project's BEND_LIB in front of it
def line(at: String, args: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, ["env", "BEND_LIB=" ++ at], args)

# a program run with this project's BEND_LIB set for it
def exec(args: List<&2, String>) -> IO(String):
  do IO<String>:
    at : String <- lib()
    R.exec(line(at, args))

# the directory `ez build` writes into: `bin` when it was not told where
def dirs.build(build: Bool, bare: Bool) -> List<&2, String>:
  match build:
    case True{}:
      Bool.pick(List<&2, String>, bare, ["bin"], [])
    case False{}:
      []

# the directories a command writes into and does not make itself: `.ez` for
# `ez check`'s JS, and `bin` for `ez build`'s default output. Every other
# command makes what it writes into when it writes, and `ez help`, `doctor`
# and the rest write nothing here, so they leave a directory as they found it.
def dirs(+cmd: String, +out: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, String.eq(cmd, "check"), [".ez"],
    dirs.build(String.eq(cmd, "build"), String.is_empty(out)))

# those directories made. Base has no mkdir, so this is coreutils, and no
# directory means no run at all.
def make(ds: List<&2, String>) -> IO(Unit):
  match ds:
    case []:
      IO.pure(Unit, Unit{})
    case h <> t:
      do IO<Unit>:
        _mk : String <- R.exec(List.append(&2, String, ["mkdir", "-p"], h <> t))
        return Unit{}

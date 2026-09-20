# ez/env: the environment ez hands to the programs it runs. Vendored packages
# live with the project rather than in ~/.bend/lib, so every `bend` ez starts
# has to be told where they are. Base has `get_env` and no `set_env`, and the
# one foreign effect execvp's what it is given, so the variable rides in front
# of the command as `env BEND_LIB=... bend ...`. `env` is coreutils and is
# execvp'd like any other program, so no shell is involved.
import Base
import ../run/run.bend as R
import ./args.bend as Args

# a value, or the fallback when the variable was unset or empty
def or_else(+v: String, +alt: String) -> String:
  Bool.pick(String, String.is_empty(v), alt, v)

# what a variable holds, with a default for when it holds nothing
def var(name: String, +alt: String) -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env(name)
    return or_else(Args.text_of(r), alt)

# where this project's packages live
def lib() -> IO(String):
  var("BEND_LIB", ".ez/lib")

# where ez was installed, so it finds the helpers it has not absorbed yet.
# `IO.args()` carries no argv[0], so a binary cannot locate itself; this is set
# by whoever installs ez and goes away with the last of the TypeScript.
def root() -> IO(String):
  var("EZ_ROOT", ".")

# the command with the project's BEND_LIB in front of it
def line(at: String, args: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, ["env", "BEND_LIB=" ++ at], args)

# a program run with this project's BEND_LIB set for it
def exec(args: List<&2, String>) -> IO(String):
  do IO<String>:
    at : String <- lib()
    R.exec(line(at, args))

# the directories every subcommand writes into. Base has no mkdir, so this is
# coreutils, and it is done once rather than by each command that needs one.
def make() -> IO(Unit):
  do IO<Unit>:
    at : String <- lib()
    _mk : String <- R.exec(["mkdir", "-p", at, ".ez", "bin"])
    return Unit{}

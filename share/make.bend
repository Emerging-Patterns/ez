# share/make: the directories a command writes into, made, and a program run
# with this project's BEND_LIB. `share/env.bend` names the directories. These
# two run a program, so they stay with the interpreter.
import Base
import 0xabe575924687afad4cee1a2c1194d639/main.bend as R
import ./env.bend as Env

# a program run with this project's BEND_LIB set for it
def exec(args: List<&2, String>) -> IO(String):
  do IO<String>:
    at : String <- Env.lib()
    R.exec(Env.line(at, args))

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

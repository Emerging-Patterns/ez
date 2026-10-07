# share/exec: a program run with this project's BEND_LIB in front of it, and
# the directories bend writes into made before it starts. share/env decides
# what the line and the directories are; this runs them, through snap's
# foreign effect, and lives apart because bend 2.0.32 fails a proof whose
# imports reach foreign code, so a law may import share/env but never this.
import Base
import 0xead4c7939c9eaca8d47da53b4496b731/main.bend as R
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

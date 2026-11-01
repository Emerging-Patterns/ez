import Base
import ../src/share/env.bend as Env

# env: the directories ez makes before a command runs. Only a command that
# writes into one without making it gets it, so `ez help`, `ez doctor` and a
# mistyped command leave the directory they ran in as they found it.

# LAW: a command other than `check` and `build` has nothing made for it
law dirs_other:
  for +cmd: String
  for +out: String
  for ec: {False{} == String.eq(cmd, "check") : Bool}
  for eb: {False{} == String.eq(cmd, "build") : Bool}
  {Env.dirs(cmd, out) == [] : List<&2, String>}

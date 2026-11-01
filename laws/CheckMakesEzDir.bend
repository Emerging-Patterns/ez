import Base
import ../src/share/env.bend as Env

# LAW: `check` has `.ez` made, where its JS goes
law dirs_check:
  for +cmd: String
  for +out: String
  for ec: {True{} == String.eq(cmd, "check") : Bool}
  {Env.dirs(cmd, out) == [".ez"] : List<&2, String>}

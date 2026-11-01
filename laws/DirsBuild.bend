import Base
import ../src/share/env.bend as Env

# LAW: `build` told nothing has `bin` made, where its binary goes
law dirs_build:
  for +cmd: String
  for +out: String
  for ec: {False{} == String.eq(cmd, "check") : Bool}
  for eb: {True{} == String.eq(cmd, "build") : Bool}
  for eo: {True{} == String.is_empty(out) : Bool}
  {Env.dirs(cmd, out) == ["bin"] : List<&2, String>}

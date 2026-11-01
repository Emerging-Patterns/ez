import Base
import ../src/share/env.bend as Env

# LAW: and `build` told where to write has nothing made in the project
law dirs_build_out:
  for +cmd: String
  for +out: String
  for ec: {False{} == String.eq(cmd, "check") : Bool}
  for eb: {True{} == String.eq(cmd, "build") : Bool}
  for eo: {False{} == String.is_empty(out) : Bool}
  {Env.dirs(cmd, out) == [] : List<&2, String>}

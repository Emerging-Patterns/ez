# ez/cache: the toolchain, named. A new bend checks and emits differently, and
# a native build hands its C to whatever `$CC` names, so both belong in the
# name. `tests/fresh.bend` records it beside a built `bin/ez.bin` and holds the
# binary to it.
import Base
import 0x103d0af04de36ab98b311e537366ec67/main.bend as R
import ../run/bend.bend as Bend
import ../ez/env.bend as Env

# the toolchain: bend's version and the C compiler it would hand its C to
def tool() -> IO(String):
  do IO<String>:
    +out : String <- Bend.version()
    +cc : String <- Env.var("CC", "cc")
    return String.trim(R.text(out)) ++ " " ++ cc

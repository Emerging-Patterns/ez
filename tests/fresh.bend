# `bin/ez.bin` is the program the end-to-end tests beside this one drive, and
# nothing in the gate builds it. A binary older than the sources it was built
# from answers for a program nobody is reading, and then every assertion those
# tests make is made against the wrong ez: the run goes green on a fix that is
# not in it, or red on a bug that was taken out an hour ago. Neither is a
# result, and both look exactly like a source bug.
#
# So the gate says so, here, once, as a test with a name. This is a test rather
# than a refusal in the runner because `ez test` runs in other people's
# projects too, where there is no `bin/ez.bin` to be stale and nothing to
# refuse; and it does not rebuild, because a gate that built the program it is
# about to grade would be grading its own work.
import Base
import ../run/run.bend as R
import ../check/kit.bend as Check

# every source the binary is compiled from that is newer than the binary.
# `check` and the `tests` directories are left out because `ez/main.bend` does
# not reach them: they are what grades ez, not what ez is made of. A missing
# binary is caught by the same walk, since `find` has nothing to compare against
# and says so.
def newer() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["find", ".", "-name", "*.bend",
      "-newer", "bin/ez.bin",
      "-not", "-path", "./.ez/*", "-not", "-path", "./.git/*",
      "-not", "-path", "./.claude/*", "-not", "-path", "./check/*",
      "-not", "-path", "*/tests/*"])
    return String.trim(R.text(out))

def main() -> IO(Unit):
  do IO<Unit>:
    +stale : String <- newer()
    Check.eq_str("bin/ez.bin is newer than every source it is built from",
      stale, "")

#|ok bin/ez.bin is newer than every source it is built from

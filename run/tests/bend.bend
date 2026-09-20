# run.bend: the version question asked the way bend will answer it. bend up to
# 2.0.16 knows only `bend --version` and 2.0.18 on knows only `bend version`,
# and the spelling a bend does not know exits non-zero — so asking one way
# reports half the bends there are as missing, and writes a lock and a cache
# key over an error message. Whichever bend is on the PATH, this holds.
import Base
import ../../run/run.bend as R
import ../../run/bend.bend as Bend
import ../../check/kit.bend as Check

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

def main() -> IO(Unit):
  do IO<Unit>:
    +out : String <- Bend.version()
    Check.eq_str("the bend on the PATH answers its version", R.code(out), "0")
    yes("and the answer is its banner and not a complaint",
      String.starts_with(String.trim(R.text(out)), "bend 2."))

#|ok the bend on the PATH answers its version
#|ok and the answer is its banner and not a complaint

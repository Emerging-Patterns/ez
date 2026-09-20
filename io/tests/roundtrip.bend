# io/file: a file written, then read back
import Base
import ../file.bend as F
import ../../check/kit.bend as Check

# a variable's text, or the fallback when it is unset
def env_or(r: Result<&1, &1, U32 & String, String>, fallback: String) -> String:
  match r:
    case Fail{_e}:
      fallback
    case Done{s}:
      s

# a writable directory. The gate runs here, but `nix flake check` runs with the
# source in the store, where nothing may be written.
def tmp() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("TMPDIR")
    return env_or(r, "/tmp")

def main() -> IO(Unit):
  do IO<Unit>:
    dir : String <- tmp()
    +at : String <- IO.pure(String, dir ++ "/ez-io-roundtrip.txt")
    +ok : Bool <- F.write(at, "one\ntwo\n")
    Check.eq_str("a file is written", Bool.show(ok), "True")
    back : Maybe<&2, String> <- F.read(at)
    Check.eq_str("and reads back the same", F.text_of(back), "one\ntwo\n")
    gone : Maybe<&2, String> <- F.read(at ++ ".not-here")
    Check.eq_str("a file that is not there reads as nothing", F.text_of(gone), "")

#|ok a file is written
#|ok and reads back the same
#|ok a file that is not there reads as nothing

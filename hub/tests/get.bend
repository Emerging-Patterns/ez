# hub: a file fetched and checked against the hash that names it
import Base
import ../hub.bend as Hub
import ../../run/run.bend as R
import ../../check/kit.bend as Check

# a run's output without the newline the program ended on
def chomp(+s: String) -> String:
  String.take(s, Nat.sub(String.length(s), 1n))

# a file:// url under the directory the test runs in. This test is about the
# digest, not the socket, so the body comes off the disk and no server has to
# be started; tests/fetch.bend is where a socket is driven.
def here(+dir: String, at: String) -> String:
  "file://" ++ dir ++ "/" ++ at

def main() -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(["pwd"])
    +dir : String <- IO.pure(String, chomp(R.text(out)))
    got : Hub.Got <- Hub.fetch(here(dir, "hub/tests/manifest.txt"), "182e9ab84416d28eef11e51eb5680c5e")
    Check.eq_str("a file that hashes right comes back", Hub.show(got),
      "have a8a411ce45f88c9659785973fe3416c2e8ae69584151db03f5997ce3eaff9a80 src/lib.bend\n")
    bad : Hub.Got <- Hub.fetch(here(dir, "hub/tests/manifest.txt"), "0000000000000000000000000000dead")
    Check.eq_str("a file that hashes wrong is refused", Hub.show(bad),
      "miss " ++ here(dir, "hub/tests/manifest.txt") ++ " does not hash to what was asked for")
    gone : Hub.Got <- Hub.fetch(here(dir, "hub/tests/nothing.txt"), "182e9ab84416d28eef11e51eb5680c5e")
    Check.eq_str("a file that is not there is a miss, not an empty body",
      String.take(Hub.show(gone), 4n), "miss")

#|ok a file that hashes right comes back
#|ok a file that hashes wrong is refused
#|ok a file that is not there is a miss, not an empty body

# ez: what a test file states its run must print, and where its binary lands
import Base
import ../test.bend as T
import ../../check/kit.bend as Check

# a test file, trailer and all
def source() -> String:
  "import Base\n" ++
  "\n" ++
  "def main() -> IO(Unit):\n" ++
  "  IO.print(\"ok one\")\n" ++
  "\n" ++
  "#|ok one\n" ++
  "#|ok two\n"

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("the trailer is the lines after each #|", T.trailer(source()), "ok one\nok two")
    Check.eq_str("a file with no trailer wants nothing", T.trailer("def main():\n  0\n"), "")
    Check.eq_str("a comment that is not a trailer is not one",
      T.trailer("# a note\n#|ok\n"), "ok")
    Check.eq_str("the binary is named for the whole path",
      T.bin("./io/tests/roundtrip.bend"), ".gate/io-tests-roundtrip")
    Check.eq_str("two tests of the same name land apart",
      T.bin("ez/tests/quiet.bend"), ".gate/ez-tests-quiet")

#|ok the trailer is the lines after each #|
#|ok a file with no trailer wants nothing
#|ok a comment that is not a trailer is not one
#|ok the binary is named for the whole path
#|ok two tests of the same name land apart

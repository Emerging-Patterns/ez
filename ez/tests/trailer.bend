# ez: what a test file states its run must print
import Base
import ../gate.bend as G
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
    Check.eq_str("the trailer is the lines after each #|", G.trailer(source()), "ok one\nok two")
    Check.eq_str("a file with no trailer wants nothing", G.trailer("def main():\n  0\n"), "")
    Check.eq_str("a comment that is not a trailer is not one",
      G.trailer("# a note\n#|ok\n"), "ok")

#|ok the trailer is the lines after each #|
#|ok a file with no trailer wants nothing
#|ok a comment that is not a trailer is not one

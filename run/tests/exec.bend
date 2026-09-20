# run: a program run with its arguments, on both lanes
import Base
import ../run.bend as R
import ../../check/kit.bend as Check

def main() -> IO(Unit):
  do IO<Unit>:
    +hi : String <- R.exec(["echo", "hi there"])
    Check.eq_str("echo prints its argument", R.text(hi), "hi there\n")
    Check.eq_str("and exits zero", R.code(hi), "0")
    +no : String <- R.exec(["false"])
    Check.eq_str("a failing program answers its status", R.code(no), "1")
    +gone : String <- R.exec(["ez-no-such-program"])
    Check.eq_str("a program that is not there answers 127", R.code(gone), "127")
    +arg : String <- R.exec(["echo", "one two", "three"])
    Check.eq_str("an argument with a space stays one argument", R.text(arg), "one two three\n")
    +shell : String <- R.exec(["echo", "$HOME;ls"])
    Check.eq_str("no shell reads the arguments", R.text(shell), "$HOME;ls\n")

#|ok echo prints its argument
#|ok and exits zero
#|ok a failing program answers its status
#|ok a program that is not there answers 127
#|ok an argument with a space stays one argument
#|ok no shell reads the arguments

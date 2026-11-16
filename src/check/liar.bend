# check/liar: a `bend` that publishes nothing and says the wrong thing about
# it, so that `ez publish`'s disagreement path can be driven rather than
# argued about. Compiled to a binary called `bend` and put in front of the real
# one on PATH, it stands in for a bend whose package walk has drifted from
# ez's. That is the one case the happy path can never catch, because the happy
# path passes whether or not the command checks anything at all.
#
# It is Bend and not a script, so the test tree stays one language, and it
# reaches no network: nothing it prints was ever uploaded anywhere.
#
#   EZ_LIAR=hash  names a package that is not the one ez computed
#   EZ_LIAR=mute  prints the two lines that hold a `0x` name in the middle of
#                 them and never the one that is a `0x` name on its own, which
#                 is what a loose pattern finds and an anchored one does not
import Base

# a name no walk would ever arrive at, since it is not the digest of anything
def other() -> String:
  "0xdeadbeefdeadbeefdeadbeefdeadbeef"

# the line the real bend prints while it mines, which holds a name mid-line
def mining(+hash: String) -> String:
  "publishing 2 files, 193 bytes, as " ++ hash ++ " (mining its proof of work)"

# the line the real bend prints last, which holds a name mid-line too
def importing(+hash: String) -> String:
  "import " ++ hash ++ "/lib.bend as Lib"

# an environment variable's text; unset, ""
def text_of(res: Result<&1, &1, U32 & String, String>) -> String:
  match res:
    case Fail{_e}:
      ""
    case Done{s}:
      s

# what the liar says: everything the real bend says, or everything but the one
# line that is an answer
def lines(mute: Bool) -> List<&2, String>:
  match mute:
    case True{}:
      [mining(other()), importing(other())]
    case False{}:
      [mining(other()), other(), importing(other())]

# every line said, in order
def say(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case []:
      IO.pure(Unit, Unit{})
    case h <> t:
      do IO<Unit>:
        IO.print(h)
        say(t)

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("EZ_LIAR")
    say(lines(String.eq(String.trim(text_of(r)), "mute")))

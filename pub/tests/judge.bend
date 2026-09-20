# pub: the decisions `ez publish` makes about bend's output and about the
# working tree, on the text bend and git actually print. `pub/LAWS.bend` states
# what holds for every input; these are the three lines bend 2.0.21 prints and
# the lines `git status --porcelain` prints, written out so that a reader can
# see what the laws are about.
import Base
import ../pub.bend as P
import ../../check/kit.bend as Check

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# the `0x` name the local hub serves the fixture package under
def hash() -> String:
  "0x7e63a5b990a375c304ed462c071214a6"

# what `bend src/lib.bend --publish` printed, line for line
def output() -> List<&2, String>:
  ["publishing 2 files, 193 bytes, as " ++ hash() ++
    " (mining its proof of work)",
   hash(),
   "import " ++ hash() ++ "/lib.bend as Lib",
   ""]

# what a verdict is called, so a test can name it
def show(s: P.Said) -> String:
  match s:
    case P.Agreed{}:
      "agreed"
    case P.Unread{}:
      "unread"
    case P.Differs{theirs}:
      "differs " ++ theirs

def main() -> IO(Unit):
  do IO<Unit>:
    yes("a bare 0x name is an answer", P.is_name(hash()))
    yes("the line bend mines on is not", Bool.not(P.is_name(
      "publishing 2 files, 193 bytes, as " ++ hash() ++
      " (mining its proof of work)")))
    yes("nor is the import line bend ends with",
      Bool.not(P.is_name("import " ++ hash() ++ "/lib.bend as Lib")))
    yes("a name one character short is not one",
      Bool.not(P.is_name("0x7e63a5b990a375c304ed462c071214a")))
    yes("nor is one written in upper case",
      Bool.not(P.is_name("0X7E63A5B990A375C304ED462C071214A6")))
    yes("nor is one with a character no digest holds",
      Bool.not(P.is_name("0x7e63a5b990a375c304ed462c071214z6")))
    Check.eq_str("the answer is the line that is a name and nothing else",
      P.answer(output()), hash())
    Check.eq_str("an output with no bare name answers nothing",
      P.answer(["publishing as " ++ hash(),
        "import " ++ hash() ++ "/x.bend as X"]),
      "")
    Check.eq_str("the same hash twice is agreement",
      show(P.judge(hash(), output())), "agreed")
    Check.eq_str("a different hash is not, and says whose it was",
      show(P.judge("0x0000000000000000000000000000beef", output())),
      "differs " ++ hash())
    Check.eq_str("an output that names no package is not agreement either",
      show(P.judge(hash(), ["nothing to see here"])), "unread")
    yes("a status that says nothing is a clean tree",
      Bool.not(P.dirty("")))
    yes("a trailing newline is not a change", Bool.not(P.dirty("\n")))
    yes("a modified file is a change", P.dirty(" M ez/cmd.bend\n"))
    yes("a staged file is a change", P.dirty("A  pub/pub.bend\n"))
    yes("an untracked file is a change", P.dirty("?? notes.txt\n"))

#|ok a bare 0x name is an answer
#|ok the line bend mines on is not
#|ok nor is the import line bend ends with
#|ok a name one character short is not one
#|ok nor is one written in upper case
#|ok nor is one with a character no digest holds
#|ok the answer is the line that is a name and nothing else
#|ok an output with no bare name answers nothing
#|ok the same hash twice is agreement
#|ok a different hash is not, and says whose it was
#|ok an output that names no package is not agreement either
#|ok a status that says nothing is a clean tree
#|ok a trailing newline is not a change
#|ok a modified file is a change
#|ok a staged file is a change
#|ok an untracked file is a change

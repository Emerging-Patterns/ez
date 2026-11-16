# proofs of laws/CappedRunWords.bend
import Base
import ../src/share/capped.bend as Capped
import ../laws/CappedRunWords.bend as Laws

def Laws.uncapped_words(_gigs, _at, _args):
  {==}

def Laws.capped_words(_gigs, _at, _args):
  {==}

def Laws.status_137_killed(_text):
  {==}

def Laws.killed_names_cap(_text, _gigs):
  {==}

# the pick reads the premise's answer
def Laws.unkilled_says_nothing(out, gigs, alive):
  Equal.cong(Bool, String,
    b => Bool.pick(String, b, "killed for memory at " ++ gigs ++ "G: raise EZ_CAP\n", ""),
    Capped.killed(out), False{}, alive)

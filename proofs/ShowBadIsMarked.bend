# proofs of laws/ShowBadIsMarked.bend
import Base
import ../src/check/eq.bend as Eq
import ../laws/ShowBadIsMarked.bend as Laws

# `error: ` is a literal, so the comparison computes down to the reason
# against the empty prefix; a name is not, so it is the append law.
def Laws.show_bad_is_marked(why):
  Eq.starts_nil(why)

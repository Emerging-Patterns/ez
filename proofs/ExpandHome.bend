# proofs of laws/ExpandHome.bend
import Base
import ../src/check/eq.bend as Eq
import ../laws/ExpandHome.bend as Laws

# `~/` is not `~`, which computes, and is a prefix of what it was put on,
# which `starts_nil` holds for the open rest
def Laws.expand_home(home, rest):
  %Equal.sym(Bool, String.starts_with(rest, ""), True{}, Eq.starts_nil(rest)) :
    {Bool.pick(String, _, home ++ String.drop("~/" ++ rest, 1n), "~/" ++ rest)
      == home ++ ("/" ++ rest) : String}
  {==}

# ez/sorted: strings in order, sorted by a walk the termination check can read.
#
# Base's List.sort takes its comparison as an erased (`~`) argument and is a
# fuelled bottom-up merge sort besides. Bend cannot show either terminates, so
# every def whose closure reaches it falls outside the proof guarantees and is
# counted unsafe. An insertion shrinks its list at every step and costs nothing,
# and the lists here are a handful of hashes.
import Base

# where one string belongs in a list already sorted, once the rest of that list
# has been placed. The recursion is done before the choice, because a def may
# not call itself inside a branch.
def sort.ins.put(le: Bool, +item: String, head: String, tail: List<&2, String>,
  rest: List<&2, String>) -> List<&2, String>:
  match le:
    case True{}:
      item <> (head <> tail)
    case False{}:
      head <> rest

# one string dropped into a sorted list
def sort.ins(+item: String, ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case []:
      [item]
    case +h <> +t:
      sort.ins.put(String.is_le(item, h), item, h, t, sort.ins(item, t))

# the strings in order. Base's List.sort takes its comparison as an erased
# argument and is fuelled besides, so nothing downstream of it can be proved;
# an insertion shrinks its list every step and stays inside the check.
def sort(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case []:
      []
    case +h <> t:
      sort.ins(h, sort(t))

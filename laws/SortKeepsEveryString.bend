# ez/sorted.bend's sort puts a list of strings in order and drops none of
# them: what it returns is as long as what it was given, and one string
# dropped into a list makes it one longer. This is internal: the runners sort
# the files they find so a report reads the same twice over, and a sort that
# lost a file would run fewer proofs than the tree holds. That the result is
# in order is not proved.
import Base
import ../src/ez/sorted.bend as Sort

# LAW: a string dropped into a list makes it one longer
law ins_adds_one:
  for +item: String
  for ss: List<&2, String>
  {List.length(&2, String, Sort.sort.ins(item, ss)) == 1n+List.length(&2, String, ss) : Nat}

# LAW: sorting keeps the list's length
law sort_keeps_length:
  for ss: List<&2, String>
  {List.length(&2, String, Sort.sort(ss)) == List.length(&2, String, ss) : Nat}

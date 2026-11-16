# What the scan benchmark (src/pkg/bench/scan.bend) answers: the mode named
# on its command line picks the classifier, `old` the one before the rewrite
# and anything else the one pkg/pkg.bend has now, each counted over the same
# lines; the program's own name is not an argument, every argument after it
# is kept, and an argument past the end reads as nothing. This is internal:
# the benchmark is a developer's tool the gate does not run.
import Base
import ../src/pkg/bench/scan.bend as B

# LAW: `old` counts with the classifier before the rewrite
law run_old:
  for mode: String
  for size: Nat
  for e: {True{} == String.eq(mode, "old") : Bool}
  {B.run(mode, size) == "old " ++ Nat.show(B.count.old(B.lines(size))) : String}

# LAW: and any other mode with the classifier as it is now
law run_new:
  for mode: String
  for size: Nat
  for e: {False{} == String.eq(mode, "old") : Bool}
  {B.run(mode, size) == "new " ++ Nat.show(B.count.new(B.lines(size))) : String}

# LAW: the program's own name is dropped and the rest kept
law args_drop_name:
  for h: String
  for t: List<&1, String>
  {B.args(Con{h, t}) == B.copy(t) : List<&2, String>}

# LAW: and copying keeps every argument
law copy_keeps_length:
  for xs: List<&1, String>
  {List.length(&2, String, B.copy(xs)) == List.length(&1, String, xs) : Nat}

# LAW: the first argument is the head
law at_first:
  for h: String
  for t: List<&2, String>
  {B.at(h <> t, 0n) == h : String}

# LAW: a later one is found in the rest
law at_later:
  for h: String
  for t: List<&2, String>
  for p: Nat
  {B.at(h <> t, 1n+p) == B.at(t, p) : String}

# LAW: and one past the end is nothing
law at_past_end:
  for index: Nat
  {B.at([], index) == "" : String}


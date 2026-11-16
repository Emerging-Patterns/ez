# What `ez test` compares with a test's trailer is the run's output with
# bend's update nag dropped wherever it appears, every other line kept in
# order, and the blank lines at its end dropped, the way a shell's `$(...)`
# drops a trailing newline. This is internal: it fixes ez/quiet.bend, which
# ez/test.bend trusts to hand it only what the program printed.
# also rests on: laws/UpdateNagAnchoredAtFront.bend
import Base
import ../src/ez/quiet.bend as Q

# LAW: the nag is dropped
law nag_dropped:
  for +h: String
  for t: List<&2, String>
  for e: {True{} == Q.is_nag(h) : Bool}
  {Q.go(h <> t) == Q.go(t) : List<&2, String>}

# LAW: and every other line is kept, in its place
law line_kept:
  for +h: String
  for t: List<&2, String>
  for e: {False{} == Q.is_nag(h) : Bool}
  {Q.go(h <> t) == h <> Q.go(t) : List<&2, String>}

# LAW: a blank line at the end changes nothing the fold collects
law blank_tail_dropped:
  for ls: List<&2, String>
  {Q.tail.walk(List.append(&2, String, ls, [""])) == Q.tail.walk(ls) : Q.Tail}

# LAW: so the text compared is the same with a blank line at its end
law chomp_blank_tail:
  for text: String
  for ls: List<&2, String>
  for e: {List.append(&2, String, ls, [""]) == String.lines(text) : List<&2, String>}
  {Q.chomp(text) == String.join(Q.chomp.lines(ls), "\n") : String}

# LAW: and a run that opens with the nag is compared without it
law filter_drops_nag:
  for text: String
  for +h: String
  for t: List<&2, String>
  for e: {h <> t == String.lines(text) : List<&2, String>}
  for nag: {True{} == Q.is_nag(h) : Bool}
  {Q.filter(text) == String.join(Q.chomp.lines(Q.go(t)), "\n") : String}

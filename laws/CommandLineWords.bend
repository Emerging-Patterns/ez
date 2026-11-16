# How ez reads the words it was started with. This is internal: it holds
# src/share/args.bend in place, under the commands that read their words.
#
# The words are every word after the program's own name, in order and
# unchanged. The nth word is the word at that place, counted from zero, and a
# place past the last word reads as no word, the empty string. A line split
# into its first word and the rest gives exactly those two. An environment
# variable that is set reads as its value, and one that is not reads as the
# empty string. What `IO.args` hands ez is trusted in src/share/args.bend.
import Base
import ../src/share/args.bend as Args

# LAW: the words ez reads are the ones after the program's name, in order
law words_after_program:
  for prog: String
  for ws: List<&1, String>
  {Args.rest(Args.copy(Con{prog, ws})) == Args.copy(ws) : List<&2, String>}

# LAW: the first word is at place zero
law word_at_zero:
  for h: String
  for t: List<&2, String>
  {Args.at(h <> t, 0n) == h : String}

# LAW: and every later place is a place of the words after it
law word_at_later:
  for h: String
  for t: List<&2, String>
  for n: Nat
  {Args.at(h <> t, 1n+n) == Args.at(t, n) : String}

# LAW: a place past the last word reads as no word
law word_past_end:
  for n: Nat
  {Args.at([], n) == "" : String}

# LAW: a line split is its first word and the words after it
law split_first:
  for h: String
  for t: List<&2, String>
  {Args.split(h <> t) == (h, t) : String & List<&2, String>}

# LAW: a variable that is set reads as its value
law env_set_reads:
  for value: String
  {Args.text_of(Done{value}) == value : String}

# LAW: a variable that is not set reads as the empty string
law env_unset_empty:
  for e: U32 & String
  {Args.text_of(Fail{e}) == "" : String}

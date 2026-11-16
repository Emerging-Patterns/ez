# What the lying `bend` (src/check/liar.bend) prints, which tests/publish.bend
# puts in front of the real one to drive `ez publish`'s disagreement path.
# This is internal: the liar is a test fixture, not part of ez.
#
# It prints the two lines the real bend prints around its answer, each
# holding a `0x` name mid-line, and, exactly when it is not mute, the answer
# itself: a line that is a `0x` name on its own. So a pattern anchored at the
# start of a line finds a name exactly when the liar is not mute, and the name
# it finds is never one a package walk arrives at. An unset EZ_LIAR reads as
# "", so the liar is mute only when it is asked to be.
import Base
import ../src/check/liar.bend as Liar

# whether a line is a `0x` name on its own, which is what an anchored pattern
# finds
def bare(+line: String) -> Bool:
  String.starts_with(line, "0x")

# whether any of the lines is one
def has_bare(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      False{}
    case h <> t:
      Bool.or(bare(h), has_bare(t))

# LAW: the liar prints a bare name exactly when it is not mute
law bare_unless_mute:
  for mute: Bool
  {has_bare(Liar.lines(mute)) == Bool.not(mute) : Bool}

# LAW: the line it prints while it mines holds the name mid-line, never at
# the start
law mining_not_bare:
  for +hash: String
  {bare(Liar.mining(hash)) == False{} : Bool}

# LAW: and so does the import line it prints last
law importing_not_bare:
  for +hash: String
  {bare(Liar.importing(hash)) == False{} : Bool}

# LAW: an EZ_LIAR that could not be read is ""
law unset_is_empty:
  for err: U32 & String
  {Liar.text_of(Fail{err}) == "" : String}

# LAW: and one that could is its text
law set_is_text:
  for text: String
  {Liar.text_of(Done{text}) == text : String}

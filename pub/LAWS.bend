# pub: the laws. The human states them; PROOF.bend must prove them.
#
# `ez publish` is mostly effect: a git run, a bend run, an upload. An effect
# proves nothing. Everything it decides, though, it decides purely: what
# counts as bend's answer, whether that answer agrees with ez's hash, and
# whether the working tree is clean enough to send. Those three are where the
# command's correctness lives, and they are what is stated here.
#
# The laws are written against the failure the command exists to prevent. A
# hash lifted out of another program's stdout by a loose pattern is a hash you
# have no reason to believe, so the laws say what the recogniser will and will
# not accept, and that no disagreement can ever be read as agreement.
import Base
import ./pub.bend as P

# whether any line of a list is a `0x` name. This is the vocabulary
# `answer_is_a_name` needs and nothing else uses: it says here what "bend
# printed a name" means, in a form Bend can walk, independently of the search
# that goes looking for one.
def any_name.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

def any_name(ls: List<&2, String>) -> Bool:
  match ls:
    case []:
      False{}
    case +h <> t:
      any_name.step(P.is_name(h), _u => any_name(t))

# LAW: ez reads a name out of bend's output exactly when bend printed one, and
# reads nothing otherwise. This is the law the bash version broke: it grepped
# for a hash and then, when that missed, grepped again for something looser, so
# an output holding no name still produced one. Here an output holding no name
# produces "" and the command stops.
law answer_is_a_name:
  for ls: List<&2, String>
  {P.is_name(P.answer(ls)) == any_name(ls) : Bool}

# LAW: the line bend prints while it mines is not an answer. bend 2.0.21 says
# `publishing 2 files, 193 bytes, as 0x<hash> (mining its proof of work)`, and
# that line holds a `0x` name in the middle of it. A pattern that looks for a
# hash anywhere in a line finds this one; the anchored one does not.
law progress_is_not_an_answer:
  for rest: String
  {P.is_name("publishing " ++ rest) == False{} : Bool}

# LAW: nor is the import line bend prints after it. That one holds the name
# too, followed by a path, and it is the line a person is most likely to be
# looking at when they write the pattern.
law import_is_not_an_answer:
  for rest: String
  {P.is_name("import " ++ rest) == False{} : Bool}

# LAW: an answer ez cannot read is never agreement. Not a shrug that reports
# ez's number anyway, and not a fallback to whatever was found: a verdict on an
# output with no name in it is `Unread`, and `Unread` does not let the command
# go on.
law unread_never_agrees:
  for +ours: String
  for +theirs: String
  for e: {False{} == P.is_name(theirs) : Bool}
  {P.agreed(P.judge.at(ours, theirs)) == False{} : Bool}

# LAW: and an answer that names a different package is never agreement either.
# This is the one that matters most, because the happy path passes without it:
# whenever bend's answer is not character for character ez's hash, the verdict
# refuses, whatever else is true of either string.
law differs_never_agrees:
  for +ours: String
  for +theirs: String
  for e: {False{} == String.eq(ours, theirs) : Bool}
  {P.agreed(P.judge.at(ours, theirs)) == False{} : Bool}

# LAW: a tree is clean exactly when `git status --porcelain` named no path at
# all. The two walks are written independently, one looking for a line that
# says something and the other checking that every line says nothing, and this
# holds them to each other. What it pins down is the edge the whole refusal
# turns on: the empty line `String.lines` makes of a trailing newline is not a
# change, and every other line is, whatever its status code says, so an
# untracked `?? path` counts and no code is quietly exempt.
law clean_is_all_blank:
  for ls: List<&2, String>
  {P.blanks(ls) == Bool.not(P.dirty.lines(ls)) : Bool}

# LAW: and the untracked case said out loud, since it is the one a reader will
# want to check rather than derive. A status that names an untracked file is a
# dirty tree.
law untracked_is_dirty:
  for path: String
  for rest: List<&2, String>
  {P.dirty.lines(("?? " ++ path) <> rest) == True{} : Bool}

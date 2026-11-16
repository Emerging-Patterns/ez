# How a progress line names a commit and a package. This is internal: it
# holds src/share/say.bend's naming in place; the rest of a line's words are
# wording, which nothing should rely on.
#
# A commit is named by its first twelve characters, and one of twelve or
# fewer is named whole. A package is named by its entry's file name without
# the directory or the `.bend`, and by its hash when that leaves nothing.
import Base
import ../src/pkg/path.bend as P
import ../src/share/say.bend as Say

# LAW: a commit of twelve characters or fewer is named whole
law short_rev_whole:
  for +rev: String
  for short: {Nat.is_le(String.length(rev), 12n) == True{} : Bool}
  {Say.brief(rev) == rev : String}

# LAW: a longer one is named by its first twelve
law long_rev_cut:
  for +rev: String
  for long: {Nat.is_le(String.length(rev), 12n) == False{} : Bool}
  {Say.brief(rev) == String.take(rev, 12n) : String}

# LAW: a package whose entry has a name is called by it
law label_names_entry:
  for hash: String
  for +entry: String
  for named: {String.is_empty(P.unbend(P.base(entry))) == False{} : Bool}
  {Say.label(hash, entry) == P.unbend(P.base(entry)) : String}

# LAW: and one whose entry leaves no name is called by its hash
law label_falls_to_hash:
  for hash: String
  for +entry: String
  for blank: {String.is_empty(P.unbend(P.base(entry))) == True{} : Bool}
  {Say.label(hash, entry) == hash : String}

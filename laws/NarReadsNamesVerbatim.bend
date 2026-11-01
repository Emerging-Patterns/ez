# The NAR walk reads every name and symlink target as the tree listing prints
# it: nothing is trimmed, and a newline stays inside the name that holds it.
#
# This guarantee is proved of the reading the NAR walk (`src/sha/nar.bend`)
# makes of its listing: every field is cut at the NUL that ends it and
# nowhere else (`nar_field_verbatim`), so a listing is read back as the
# fields it was printed from (`nar_listing_verbatim`), whatever spaces or
# newlines a name or target holds. That the listing is what the filesystem
# holds, and that the walk builds the NAR from it as nix's dumper does, is
# trusted in src/sha/nar.bend.
import Base
import ../src/add/world.bend as A
import ../src/sha/nar.bend as Nar

# LAW: a field of the listing the NAR walk reads is cut exactly where its NUL
# is, and nowhere else. A name or a link target holds no NUL, so it comes back
# as `find` printed it: a space at either end is kept and a newline inside it
# stays inside it.
law nar_field_verbatim:
  for x: String
  for +rest: String
  for +c: {Nar.clean(x) == True{} : Bool}
  {Nar.cut(String.append(x, SCon{Nar.nul(), rest})) == x <> Nar.cut(rest)
    : List<&2, String>}

# LAW: so a whole listing is read back as the fields it was printed from,
# each of them as it was
law nar_listing_verbatim:
  for fs: List<&2, String>
  for +c: {Nar.clean.all(fs) == True{} : Bool}
  {Nar.cut(Nar.joined(fs)) == fs : List<&2, String>}

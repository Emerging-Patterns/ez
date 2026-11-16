# The form ez writes a NAR hash in, which is the form fetchgit records as
# narHash. This is internal: it holds src/sha/nar.bend's encoding in place.
#
# A tree's NAR is the magic string `nix-archive-1`, as a NAR string, followed
# by the tree's root node. A NAR hash is `sha256-` followed by the standard
# base64 of the digest. Base64 turns every three bytes into four characters,
# group by group from the front, and pads a last group of one or two bytes
# with `=` to four characters, so a digest's base64 is never cut short. That
# the digest is SHA-256 is share/sha's, proved there.
import Base
import ../src/sha/nar.bend as Nar

# LAW: a NAR is the magic string followed by the root node
law nar_archive_magic:
  for node: String
  {Nar.archive(node) == String.append(Nar.str("nix-archive-1"), node) : String}

# LAW: every NAR hash ez writes starts `sha256-`
law sri_names_sha256:
  for bytes: String
  {String.starts_with(Nar.sri(bytes), "sha256-") == True{} : Bool}

# LAW: base64 encodes three bytes at a time from the front, each group on its
# own
law b64_by_groups_of_three:
  for a: Char
  for b: Char
  for c: Char
  for rest: String
  {Nar.b64(SCon{a, SCon{b, SCon{c, rest}}})
    == String.append(Nar.b64(SCon{a, SCon{b, SCon{c, SNil{}}}}), Nar.b64(rest)) : String}

# LAW: a last group of one byte is padded to four characters
law b64_pads_one:
  for a: Char
  {String.length(Nar.b64(SCon{a, SNil{}})) == 4n : Nat}

# LAW: and a last group of two bytes is too
law b64_pads_two:
  for a: Char
  for b: Char
  {String.length(Nar.b64(SCon{a, SCon{b, SNil{}}})) == 4n : Nat}

# LAW: a whole group of three bytes is four characters
law b64_three_is_four:
  for a: Char
  for b: Char
  for c: Char
  {String.length(Nar.b64(SCon{a, SCon{b, SCon{c, SNil{}}}})) == 4n : Nat}

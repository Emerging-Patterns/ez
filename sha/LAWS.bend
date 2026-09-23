# sha: the laws. The human states them; PROOF.bend must prove them. The digest
# itself is Giulio2002/bend-sha256's, proved there against FIPS 180-4, so what
# is stated here is the encoding `Sha.hex` puts in front of it: a text is
# hashed as its UTF-8 bytes, the way `bend --publish` and the hub hash it.
import Base
import ../sha/sha.bend as Sha
import ../sha/nar.bend as Nar
import ../pkg/pkg.bend as K
import ../pkg/LAWS.bend as PL

# LAW: the UTF-8 of two texts joined is their UTF-8 bytes joined. Each
# character is encoded on its own, never with a neighbour, so a file's bytes
# do not depend on where it was cut into pieces.
law utf8_append:
  for a: String
  for +b: String
  {Sha.utf8(String.append(a, b))
    == String.append(Sha.utf8(a), Sha.utf8(b)) : String}

# LAW: a directory's NAR is the same bytes whatever order its entries were
# listed in, so long as no name is listed twice, which a directory never does.
# `find` lists a directory in whatever order the filesystem keeps it, and two
# machines may keep it differently; this is why their narHash still agrees.
# `perm` and `distinct` are pkg's: an entry is a `K.File` holding its name and
# its node's serial, so a rearranged directory is a rearranged file list.
# Every directory the walk serializes goes through `Nar.dir`, children and
# root alike, so the law at one level is the law for the whole tree.
# EZ-HASH-2
law nar_dir_order_free:
  for +ns: List<&2, Nat>
  for +es: List<&2, K.File>
  for +dis: {PL.distinct(es) == True{} : Bool}
  {Nar.dir(PL.perm(ns, es)) == Nar.dir(es) : String}

# LAW: a field of the listing the NAR walk reads is cut exactly where its NUL
# is, and nowhere else. A name or a link target holds no NUL, so it comes back
# as `find` printed it: a space at either end is kept and a newline inside it
# stays inside it.
# EZ-HASH-7
law nar_field_verbatim:
  for x: String
  for +rest: String
  for +c: {Nar.clean(x) == True{} : Bool}
  {Nar.cut(String.append(x, SCon{Nar.nul(), rest})) == x <> Nar.cut(rest)
    : List<&2, String>}

# LAW: so a whole listing is read back as the fields it was printed from,
# each of them as it was
# EZ-HASH-7
law nar_listing_verbatim:
  for fs: List<&2, String>
  for +c: {Nar.clean.all(fs) == True{} : Bool}
  {Nar.cut(Nar.joined(fs)) == fs : List<&2, String>}

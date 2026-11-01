# The digest itself is noah-emp/bend-sha256's, proved there against FIPS
# 180-4 (trusted in src/share/sha.bend), so what is stated here is the
# encoding `Sha.hex` puts in front of it: a text is hashed as its UTF-8
# bytes, the way `bend --publish` and the hub hash it.
import Base
import ../src/share/sha.bend as Sha

# LAW: the UTF-8 of two texts joined is their UTF-8 bytes joined. Each
# character is encoded on its own, never with a neighbour, so a file's bytes
# do not depend on where it was cut into pieces.
law utf8_append:
  for a: String
  for +b: String
  {Sha.utf8(String.append(a, b))
    == String.append(Sha.utf8(a), Sha.utf8(b)) : String}

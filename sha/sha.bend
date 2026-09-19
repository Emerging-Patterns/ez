# sha/sha: the sha256 a package hash is built from. The digest itself comes from
# Giulio2002/bend-sha256, which proves its output equal to an executable FIPS
# 180-4 specification; this file is only the string-in, hex-out shape ez uses.
import Base
import 0x0a5c2c95283e42e081da247c84debe18/sha256.bend as S

# the hex sha256 digest of a string's bytes
def hex(s: String) -> String:
  S.hex(S.sha256(S.ascii(s)))

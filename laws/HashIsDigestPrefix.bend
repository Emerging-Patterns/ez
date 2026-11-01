import Base
import ../src/pkg/pkg.bend as K
import ../src/share/sha.bend as Sha
import ../src/add/world.bend as A

# LAW: the `0x` name a file set is published under is the first
# thirty-two hex characters of the manifest's digest. A lock that pins
# `0x<hash>` pins this prefix, and nothing else of the digest.
law hash_is_prefix:
  for xs: List<&2, K.Item>
  {K.hash_of(xs) == "0x" ++ String.take(Sha.hex(K.manifest_of(xs)), 32n)
    : String}

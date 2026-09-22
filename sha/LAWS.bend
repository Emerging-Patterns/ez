# sha: the laws. The human states them; PROOF.bend must prove them. The digest
# itself is Giulio2002/bend-sha256's, proved equal to an executable FIPS 180-4
# specification. This package is only the string-in, hex-out shape ez uses, so
# what is stated here is that shape: the empty string, the FIPS vector, and a
# manifest line hash to the hex the rest of ez takes a package name over. The
# NAR SRI laws hold the empty-tree hash to what `nix hash path --sri` prints.
import Base
import ./sha.bend as Sha
import ./nar.bend as Nar

# LAW: the empty string hashes to the FIPS 180-4 empty digest. A package that
# found no bytes still has a name, and that name is this hex, not a blank.
law hex_empty:
  {Sha.hex("")
    == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    : String}

# LAW: "abc" hashes to the FIPS 180-4 vector. The wrapper is the digest the
# specification names, in the hex ez writes.
law hex_abc:
  {Sha.hex("abc")
    == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    : String}

# LAW: a manifest line hashes to the digest a package hash is taken over. The
# `0x` name a package is published under is this hex, cut to thirty-two
# characters, so a wrong digest here is a different package.
law hex_manifest:
  {Sha.hex(
    "a8a411ce45f88c9659785973fe3416c2e8ae69584151db03f5997ce3eaff9a80 src/lib.bend\n")
    == "182e9ab84416d28eef11e51eb5680c5e868655059b4a3b859161abf89b392109"
    : String}

# LAW: the SRI of the empty digest is the base64 of those thirty-two bytes.
law sri_empty_digest:
  {Nar.sri.hex("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    == "sha256-47DEQpj8HBSa+/TImW+5JCeuQeRkm5NMpJWZG3hSuFU="
    : String}

# LAW: an empty directory's NAR hashes to the SRI `nix hash path --sri` prints
# for an empty directory. The weigh path strips `.git` and asks for this shape.
law sri_empty_dir:
  {Nar.sri(Nar.archive(Nar.empty()))
    == "sha256-pQpattmS9VmO3ZIQUFn66az8GSmB4IvYhTTCFn6SUmo="
    : String}

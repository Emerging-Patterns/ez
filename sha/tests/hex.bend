# sha: the digests a package hash is built from
import Base
import ../sha.bend as Sha
import ../../check/kit.bend as Check

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("the empty string", Sha.hex(""),
      "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    Check.eq_str("abc, the FIPS 180-4 vector", Sha.hex("abc"),
      "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
    Check.eq_str("a manifest line, as a package hash is taken over", Sha.hex(
      "a8a411ce45f88c9659785973fe3416c2e8ae69584151db03f5997ce3eaff9a80 src/lib.bend\n"),
      "182e9ab84416d28eef11e51eb5680c5e868655059b4a3b859161abf89b392109")

#|ok the empty string
#|ok abc, the FIPS 180-4 vector
#|ok a manifest line, as a package hash is taken over

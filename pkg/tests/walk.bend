# pkg: the import walk over a real tree. `tests/fixture` is the layout that
# makes a package interesting: a nested module, a foreign body beside it, and a
# module above the entry's own directory. The hash asserted here is the one
# `bend --publish` minted for exactly these bytes at a local hub, and
# `tests/publish.sh` mints it again.
import Base
import ../pkg.bend as K
import ../../check/kit.bend as Check

# where each file of a package sits inside it
def ats(fs: List<&2, K.File>) -> List<&2, String>:
  match fs:
    case []:
      []
    case h <> t:
      K.file.at(h) <> ats(t)

# the fixture's package, taken apart onto one line: the root it re-rooted at,
# its hash, and where every file of it sits
def shown(+p: K.Pkg) -> String:
  K.pkg.root(p) ++ " " ++ K.pkg.hash(p) ++ " " ++ String.join(ats(K.pkg.files(p)), " ")

def main() -> IO(Unit):
  do IO<Unit>:
    p : K.Pkg <- K.pkg_of("tests/fixture/src/lib.bend")
    Check.eq_str("a module reached through `..` re-roots the package", shown(p),
      "tests/fixture 0x4b8dabac9254cf301082e7cc367f1287 other/up.bend " ++
      "src/lib.bend src/util/beep.c src/util/beep.js src/util/math.bend")

#|ok a module reached through `..` re-roots the package

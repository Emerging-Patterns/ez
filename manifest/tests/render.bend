# manifest: a ledger rendered back to ez.toml, added to, and removed from
import Base
import ../manifest.bend as M
import ../render.bend as R
import ../../check/kit.bend as Check

# a ledger edited, then rendered, then read back and rendered again, which is
# what `ez add` and `ez remove` do to the file on disk
def edited(manifest: M.Manifest) -> String:
  R.show(manifest)

def main() -> IO(Unit):
  do IO<Unit>:
    +one : M.Manifest <- IO.pure(M.Manifest, M.Manifest{"a", "m.bend", "", [], []})
    Check.eq_str("a ledger with no dependencies", R.show(one),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n")
    Check.eq_str("a dependency added", edited(R.add(one,
      M.Dep{"x", "0xabc", "", M.Hub{}})),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n\n[deps.x]\nhash = \"0xabc\"\n")
    Check.eq_str("a dependency removed", edited(R.remove(
      R.add(one, M.Dep{"x", "0xabc", "", M.Hub{}}), "x")),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n")

#|ok a ledger with no dependencies
#|ok a dependency added
#|ok a dependency removed

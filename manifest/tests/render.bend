# manifest: a ledger rendered back to ez.toml, added to, and removed from
import Base
import ../manifest.bend as M
import ../render.bend as R
import ../toml.bend as T
import ../../check/kit.bend as Check

# a document of nested tables, the shape a lock file takes
def doc() -> List<&2, T.Sect>:
  [T.Sect{"lock", [T.Kv{"hub", "https://hub.bend-lang.com"}]},
   T.Sect{"packages." ++ T.quote("0xaa") ++ ".files",
     [T.Kv{"src/lib.bend", "ab"}]}]

# the sections of a document that parsed, shown as `name key=value ..` lines
def shape(t: T.Toml) -> String:
  String.join(T.show.sects(T.sects(t)), " ")

# a ledger edited, then rendered, then read back and rendered again, which is
# what `ez add` and `ez remove` do to the file on disk
def edited(m: M.Manifest) -> String:
  R.show(m)

def main() -> IO(Unit):
  do IO<Unit>:
    +one : M.Manifest <- IO.pure(M.Manifest, M.Manifest{"a", "m.bend", []})
    Check.eq_str("a ledger with no dependencies", R.show(one),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n")
    Check.eq_str("a dependency added", edited(R.add(one,
      M.Dep{"x", "0xabc", "", M.Hub{}})),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n\n[deps.x]\nhash = \"0xabc\"\n")
    Check.eq_str("a dependency removed", edited(R.remove(
      R.add(one, M.Dep{"x", "0xabc", "", M.Hub{}}), "x")),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n")
    Check.eq_str("a nested table renders with its path quoted where it must be",
      T.render(doc()),
      "[lock]\nhub = \"https://hub.bend-lang.com\"\n\n" ++
      "[packages.\"0xaa\".files]\n\"src/lib.bend\" = \"ab\"\n")
    Check.eq_str("a rendered document reads back as what it was",
      shape(T.parse(T.render(doc()))),
      "lock hub=https://hub.bend-lang.com packages.\"0xaa\".files src/lib.bend=ab")

#|ok a ledger with no dependencies
#|ok a dependency added
#|ok a dependency removed
#|ok a nested table renders with its path quoted where it must be
#|ok a rendered document reads back as what it was

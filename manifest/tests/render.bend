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

def text() -> String:
  "[package]\n" ++
  "name = \"myapp\"\n" ++
  "entry = \"src/main.bend\"\n" ++
  "\n[deps.json]\n" ++
  "hash = \"0x1111111111111111111111111111aaaa\"\n" ++
  "\n[deps.wire]\n" ++
  "hash = \"0x7e63a5b990a375c304ed462c071214a6\"\n" ++
  "git = \"https://github.com/owner/repo\"\n" ++
  "rev = \"16773c0aa9914b5f04d062469d50100111eb9c9c\"\n" ++
  "tag = \"v1.0\"\n" ++
  "entry = \"src/lib.bend\"\n"

# a ledger edited, then rendered, then read back and rendered again, which is
# what `ez add` and `ez remove` do to the file on disk
def edited(m: M.Manifest) -> String:
  R.show(m)

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("what was read renders back to itself", R.render(M.parse(text())), text())
    Check.eq_str("a ledger that would not parse renders as nothing",
      R.render(M.parse("[package\n")), "")
    +one : M.Manifest <- IO.pure(M.Manifest, M.Manifest{"a", "m.bend", []})
    Check.eq_str("a ledger with no dependencies", R.show(one),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n")
    Check.eq_str("a dependency added", edited(R.add(one,
      M.Dep{"x", "0xabc", "", M.Hub{}})),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n\n[deps.x]\nhash = \"0xabc\"\n")
    Check.eq_str("adding the same name twice replaces it", edited(R.add(
      R.add(one, M.Dep{"x", "0xold", "", M.Hub{}}), M.Dep{"x", "0xnew", "", M.Hub{}})),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n\n[deps.x]\nhash = \"0xnew\"\n")
    Check.eq_str("a dependency removed", edited(R.remove(
      R.add(one, M.Dep{"x", "0xabc", "", M.Hub{}}), "x")),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n")
    Check.eq_str("removing one that is not there changes nothing", edited(R.remove(one, "zz")),
      "[package]\nname = \"a\"\nentry = \"m.bend\"\n")
    Check.eq_str("a nested table renders with its path quoted where it must be",
      T.render(doc()),
      "[lock]\nhub = \"https://hub.bend-lang.com\"\n\n" ++
      "[packages.\"0xaa\".files]\n\"src/lib.bend\" = \"ab\"\n")
    Check.eq_str("a rendered document reads back as what it was",
      shape(T.parse(T.render(doc()))),
      "lock hub=https://hub.bend-lang.com packages.\"0xaa\".files src/lib.bend=ab")

#|ok what was read renders back to itself
#|ok a ledger that would not parse renders as nothing
#|ok a ledger with no dependencies
#|ok a dependency added
#|ok adding the same name twice replaces it
#|ok a dependency removed
#|ok removing one that is not there changes nothing
#|ok a nested table renders with its path quoted where it must be
#|ok a rendered document reads back as what it was

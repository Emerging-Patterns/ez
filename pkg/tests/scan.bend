# pkg: the import scanner, and the manifest a file set hashes to
import Base
import ../pkg.bend as K
import ../../check/kit.bend as Check

# a source file with a header, a foreign body further down, and a line that is
# an import in shape but not in the header
def text() -> String:
  "# a module\n" ++
  "import Base\n" ++
  "import ./util/math.bend as M\n" ++
  "import ../other/up.bend as U\n" ++
  "import 0xaaaabbbbccccddddeeeeffff00001111/lib.bend as L\n" ++
  "\n" ++
  "# the number, from the foreign side\n" ++
  "def ring(x: String) -> IO(String):\n" ++
  "  import \"./beep.c\"\n" ++
  "  import \"./beep.js\"\n" ++
  "\n" ++
  "import ./late.bend as Late\n"

# every module the header imports, hub packages and all
def mods(s: String) -> String:
  String.join(K.scan.mods(K.scan(s)), " ")

# every foreign body the file imports
def foreign(s: String) -> String:
  String.join(K.scan.foreign(K.scan(s)), " ")

# two files, one of them named through a directory
def files() -> List<&2, K.File>:
  [K.File{"a.bend", "ab"},
   K.File{"util/math.bend",
     "7f83b1657ff1fc53b92dc18148a1d65dfc2d4b1fa3d677284addd200126d9069"}]

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("the header's modules, in the order written", mods(text()),
      "./util/math.bend ../other/up.bend 0xaaaabbbbccccddddeeeeffff00001111/lib.bend")
    Check.eq_str("a foreign body is found wherever it sits", foreign(text()),
      "./beep.c ./beep.js")
    Check.eq_str("an import after the header has ended is not one",
      mods("import ./a.bend as A\ndef x() -> U32:\n  1\nimport ./b.bend as B\n"),
      "./a.bend")
    Check.eq_str("a hub import names a package, not a module",
      Bool.show(K.is_hub("0xaaaa/lib.bend")), "True")
    Check.eq_str("a relative import names a module",
      Bool.show(K.is_hub("./lib.bend")), "False")
    Check.eq_str("a manifest is its files in path order",
      K.manifest_of(files()),
      "ab a.bend\n7f83b1657ff1fc53b92dc18148a1d65dfc2d4b1fa3d677284addd200126d9069 util/math.bend\n")
    Check.eq_str("the hash is the first 32 hex of the manifest's digest",
      K.hash_of(files()), "0x163964b17e66f0355fb054d30b376df1")

#|ok the header's modules, in the order written
#|ok a foreign body is found wherever it sits
#|ok an import after the header has ended is not one
#|ok a hub import names a package, not a module
#|ok a relative import names a module
#|ok a manifest is its files in path order
#|ok the hash is the first 32 hex of the manifest's digest

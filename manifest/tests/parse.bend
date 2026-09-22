# manifest: the dependency ledger, read out of ez.toml
import Base
import ../manifest.bend as M
import ../../check/kit.bend as Check

# the manifest of a project with one hub dep and one git dep
def text() -> String:
  "# the project\n" ++
  "[package]\n" ++
  "name = \"myapp\"\n" ++
  "entry = \"src/main.bend\"\n" ++
  "\n" ++
  "[deps.json]\n" ++
  "hash = \"0x1111111111111111111111111111aaaa\"\n" ++
  "\n" ++
  "[deps.wire]\n" ++
  "hash = \"0x7e63a5b990a375c304ed462c071214a6\"\n" ++
  "git = \"https://github.com/owner/repo\"\n" ++
  "rev = \"16773c0aa9914b5f04d062469d50100111eb9c9c\"\n" ++
  "tag = \"v1.0\"\n" ++
  "entry = \"src/lib.bend\"\n"

# the parsed manifest, or the error, shown as one line
def shown(toml: String) -> String:
  M.show(M.parse(toml))

def main() -> IO(Unit):
  do IO<Unit>:
    Check.eq_str("the package name and entry", shown(text()),
      "myapp src/main.bend json=0x1111111111111111111111111111aaaa@hub wire=0x7e63a5b990a375c304ed462c071214a6@git")
    Check.eq_str("a dep names its git rev", M.rev_of(M.parse(text()), "wire"),
      "16773c0aa9914b5f04d062469d50100111eb9c9c")
    Check.eq_str("a dep remembers the tag it was asked for", M.tag_of(M.parse(text()), "wire"), "v1.0")
    Check.eq_str("a hub dep has no rev", M.rev_of(M.parse(text()), "json"), "")
    Check.eq_str("a dep with no hash is an error", shown("[deps.x]\ngit = \"u\"\n"),
      "error: deps.x has no hash")
    Check.eq_str("a key outside a section is an error", shown("name = \"x\"\n"),
      "error: name = is outside any section")

#|ok the package name and entry
#|ok a dep names its git rev
#|ok a dep remembers the tag it was asked for
#|ok a hub dep has no rev
#|ok a dep with no hash is an error
#|ok a key outside a section is an error

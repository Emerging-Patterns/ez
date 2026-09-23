# `ez init` scaffolds a project: the ledger, the ignore rules, and an entry
# that checks. A second run leaves an entry that is already there.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../ez/quiet.bend as Q
import ../check/kit.bend as Check
import ../check/world.bend as W

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# the entry `ez init` writes when the directory does not already hold one
def stub() -> String:
  "import Base\n\ndef main() -> IO(Unit):\n  IO.print(\"hello\")"

# a fresh directory after `ez init` with nothing named
def fresh(+repo: String, +app: String) -> IO(Unit):
  do IO<Unit>:
    W.mkdir(app)
    +out : String <- R.exec(W.ez(repo, app, ["init"]))
    yes("init succeeds with no arguments", R.ok(out))
    t : Maybe<&2, String> <- F.read(app ++ "/ez.toml")
    Check.eq_str("and writes a ledger for app at main.bend",
      Q.chomp(F.text_of(t)),
      "[package]\nname = \"app\"\nentry = \"main.bend\"")
    g : Maybe<&2, String> <- F.read(app ++ "/.gitignore")
    Check.eq_str("and the ignore rules for what ez will generate",
      Q.chomp(F.text_of(g)),
      "# written by ez\n.ez/*\n!.ez/lib\n.ez/lib/*\nbin/app.out")
    e : Maybe<&2, String> <- F.read(app ++ "/main.bend")
    Check.eq_str("and an entry that checks and runs",
      Q.chomp(F.text_of(e)), stub())
    +ck : String <- R.exec(W.ez(repo, app, ["check"]))
    Check.eq_str("and that entry checks", Q.chomp(R.text(ck)), "ok main.bend")

# a second init leaves a program that is already there
def kept(+repo: String, +app: String) -> IO(Unit):
  do IO<Unit>:
    _w : Bool <- F.write(app ++ "/main.bend",
      "import Base\n\ndef main() -> U32:\n  7\n")
    _i : String <- R.exec(W.ez(repo, app, ["init"]))
    e : Maybe<&2, String> <- F.read(app ++ "/main.bend")
    Check.eq_str("a second init leaves the entry it found",
      Q.chomp(F.text_of(e)), "import Base\n\ndef main() -> U32:\n  7")
    g : Maybe<&2, String> <- F.read(app ++ "/.gitignore")
    Check.eq_str("and does not rewrite the ignore file",
      Q.chomp(F.text_of(g)),
      "# written by ez\n.ez/*\n!.ez/lib\n.ez/lib/*\nbin/app.out")

# an entry under a directory that is not there yet
def nested(+repo: String, +app: String) -> IO(Unit):
  do IO<Unit>:
    W.mkdir(app)
    +out : String <- R.exec(W.ez(repo, app, ["init", "myapp", "src/main.bend"]))
    yes("init succeeds with a nested entry", R.ok(out))
    e : Maybe<&2, String> <- F.read(app ++ "/src/main.bend")
    Check.eq_str("and writes the entry under the directories it needs",
      Q.chomp(F.text_of(e)), stub())
    t : Maybe<&2, String> <- F.read(app ++ "/ez.toml")
    Check.eq_str("and names that entry in the ledger",
      Q.chomp(F.text_of(t)),
      "[package]\nname = \"myapp\"\nentry = \"src/main.bend\"")
    +ck : String <- R.exec(W.ez(repo, app, ["check"]))
    Check.eq_str("and that nested entry checks", Q.chomp(R.text(ck)),
      "ok src/main.bend")

# an entry that was already there is left alone
def existing(+repo: String, +app: String) -> IO(Unit):
  do IO<Unit>:
    W.mkdir(app ++ "/src")
    _w : Bool <- F.write(app ++ "/src/lib.bend",
      "import Base\n\ndef double(+x: U32) -> U32:\n  (x * 2 : U32)\n")
    _i : String <- R.exec(W.ez(repo, app, ["init", "myapp", "src/lib.bend"]))
    e : Maybe<&2, String> <- F.read(app ++ "/src/lib.bend")
    Check.eq_str("init does not overwrite an entry that is already there",
      Q.chomp(F.text_of(e)),
      "import Base\n\ndef double(+x: U32) -> U32:\n  (x * 2 : U32)")

def go(+repo: String, +root: String) -> IO(Unit):
  do IO<Unit>:
    fresh(repo, root ++ "/fresh")
    kept(repo, root ++ "/fresh")
    nested(repo, root ++ "/nested")
    existing(repo, root ++ "/existing")
    W.rm(root)

def main() -> IO(Unit):
  do IO<Unit>:
    repo : String <- W.here()
    root : String <- W.tmp()
    go(repo, root)

#|ok init succeeds with no arguments
#|ok and writes a ledger for app at main.bend
#|ok and the ignore rules for what ez will generate
#|ok and an entry that checks and runs
#|ok and that entry checks
#|ok a second init leaves the entry it found
#|ok and does not rewrite the ignore file
#|ok init succeeds with a nested entry
#|ok and writes the entry under the directories it needs
#|ok and names that entry in the ledger
#|ok and that nested entry checks
#|ok init does not overwrite an entry that is already there

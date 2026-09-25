# A ledger and a lock as ez wrote them before it used eztoml 0.4, and as it
# writes them now. Each old one reads to the same sections and the same model
# as its new form, and writing either gives the new form, byte for byte: the
# old files in every Emerging-Patterns repository keep reading, and ez writes
# one layout. The step checked is `toml/toml.bend`'s, between eztoml's
# document and ez's sections, which no law covers (EZ-TRUST-8).
import Base
import ../toml/toml.bend as T
import ../ledger/manifest.bend as M
import ../ledger/render.bend as Rend
import ../check/kit.bend as Check

# a ledger as ez wrote it before: quoted strings, a bare `vendor = true`, and
# a blank line before each table
def old.ledger() -> String:
  "[package]\nname = \"app\"\nentry = \"src/main.bend\"\n" ++
  "\n[deps.wire]\nhash = \"0x7e63a5b990a375c304ed462c071214a6\"\n" ++
  "git = \"https://github.com/owner/repo\"\nrev = \"16773c0aa9914b5f04d062469d50100111eb9c9c\"\n" ++
  "tag = \"v1.0\"\nroot = \".\"\nnarHash = \"sha256-abc=\"\nvendor = true\nentry = \"src/lib.bend\"\n" ++
  "\n[deps.bend-tensors]\nhash = \"0x39d8166231e68361eb37e8bef9287b8a\"\n" ++
  "hub = \"bend-tensors@0.0.0.2\"\nentry = \"tensors.bend\"\n" ++
  "\n[tools.bolt]\ngit = \"https://github.com/Emerging-Patterns/bolt\"\n" ++
  "rev = \"38da7d930a9251f44cf7434032e954b2e706564b\"\ntag = \"v1.7.0\"\nroot = \".\"\n" ++
  "narHash = \"sha256-def=\"\n"

# a lock as ez wrote it before: each package's tables under a quoted hash
def old.lock() -> String:
  "[lock]\nversion = \"2\"\nhub = \"https://hub.bend-lang.com\"\n" ++
  "\n[packages.\"0x7e63a5b990a375c304ed462c071214a6\".source]\nkind = \"git\"\n" ++
  "url = \"https://github.com/owner/repo\"\nrev = \"16773c0aa9914b5f04d062469d50100111eb9c9c\"\n" ++
  "entry = \"src/lib.bend\"\nroot = \".\"\nnarHash = \"sha256-abc=\"\ntag = \"v1.0\"\n" ++
  "\n[packages.\"0x7e63a5b990a375c304ed462c071214a6\".files]\n" ++
  "LICENSE = \"309f5aae946e4db157750e002fb179a74ed0fe27fce09a7be68a6977b14f205f\"\n" ++
  "\"src/lib.bend\" = \"fff16a9f901df7150ec13b5488820e8fe4ca288133c3cf2e4fcc04ec6a3671f9\"\n" ++
  "\n[names]\n\"bend-tensors@0.0.0.2\" = \"0x39d8166231e68361eb37e8bef9287b8a\"\n" ++
  "\n[tools.bolt]\ngit = \"https://github.com/Emerging-Patterns/bolt\"\n" ++
  "rev = \"38da7d930a9251f44cf7434032e954b2e706564b\"\nroot = \".\"\nnarHash = \"sha256-def=\"\n"

# a document's sections, each as its header's segments and its pairs
def sect.show(sect: T.Sect) -> String:
  T.Sect{nn, ps} = sect
  String.join(T.segments(nn), "|") ++ " " ++ String.join(T.show.kvs(ps), " ")

def sects.show(ss: List<&2, T.Sect>) -> String:
  match ss:
    case []:
      ""
    case hd <> tl:
      sect.show(hd) ++ "\n" ++ sects.show(tl)

# what a text reads to, section by section, and whether it read without error
def read.of(doc: T.Toml) -> String:
  T.Toml{bad, _name, _pairs, done} = doc
  "bad=" ++ bad ++ "\n" ++ sects.show(done)

def read(+text: String) -> String:
  read.of(T.parse(text))

# the ledger above, as ez writes it now: eztoml writes the tables a dotted
# header implies, and no blank lines
def new.ledger() -> String:
    "[package]\n" ++
    "name = \"app\"\n" ++
    "entry = \"src/main.bend\"\n" ++
    "[deps]\n" ++
    "[deps.wire]\n" ++
    "hash = \"0x7e63a5b990a375c304ed462c071214a6\"\n" ++
    "git = \"https://github.com/owner/repo\"\n" ++
    "rev = \"16773c0aa9914b5f04d062469d50100111eb9c9c\"\n" ++
    "tag = \"v1.0\"\n" ++
    "root = \".\"\n" ++
    "narHash = \"sha256-abc=\"\n" ++
    "vendor = true\n" ++
    "entry = \"src/lib.bend\"\n" ++
    "[deps.bend-tensors]\n" ++
    "hash = \"0x39d8166231e68361eb37e8bef9287b8a\"\n" ++
    "hub = \"bend-tensors@0.0.0.2\"\n" ++
    "entry = \"tensors.bend\"\n" ++
    "[tools]\n" ++
    "[tools.bolt]\n" ++
    "git = \"https://github.com/Emerging-Patterns/bolt\"\n" ++
    "rev = \"38da7d930a9251f44cf7434032e954b2e706564b\"\n" ++
    "tag = \"v1.7.0\"\n" ++
    "root = \".\"\n" ++
    "narHash = \"sha256-def=\"\n"

# the lock above, as ez writes it now: a package's hash is a bare key
def new.lock() -> String:
    "[lock]\n" ++
    "version = \"2\"\n" ++
    "hub = \"https://hub.bend-lang.com\"\n" ++
    "[packages]\n" ++
    "[packages.0x7e63a5b990a375c304ed462c071214a6]\n" ++
    "[packages.0x7e63a5b990a375c304ed462c071214a6.source]\n" ++
    "kind = \"git\"\n" ++
    "url = \"https://github.com/owner/repo\"\n" ++
    "rev = \"16773c0aa9914b5f04d062469d50100111eb9c9c\"\n" ++
    "entry = \"src/lib.bend\"\n" ++
    "root = \".\"\n" ++
    "narHash = \"sha256-abc=\"\n" ++
    "tag = \"v1.0\"\n" ++
    "[packages.0x7e63a5b990a375c304ed462c071214a6.files]\n" ++
    "LICENSE = \"309f5aae946e4db157750e002fb179a74ed0fe27fce09a7be68a6977b14f205f\"\n" ++
    "\"src/lib.bend\" = \"fff16a9f901df7150ec13b5488820e8fe4ca288133c3cf2e4fcc04ec6a3671f9\"\n" ++
    "[names]\n" ++
    "\"bend-tensors@0.0.0.2\" = \"0x39d8166231e68361eb37e8bef9287b8a\"\n" ++
    "[tools]\n" ++
    "[tools.bolt]\n" ++
    "git = \"https://github.com/Emerging-Patterns/bolt\"\n" ++
    "rev = \"38da7d930a9251f44cf7434032e954b2e706564b\"\n" ++
    "root = \".\"\n" ++
    "narHash = \"sha256-def=\"\n"

# the sections the ledger above holds, as eztoml v0.1.0 read them: one per
# table ez wrote, and none for a table a dotted header only implies
def old.ledger.sects() -> String:
    "bad=\n" ++
    "package name=app entry=src/main.bend\n" ++
    "deps|wire hash=0x7e63a5b990a375c304ed462c071214a6 git=https://github.com/owner/repo rev=16773c0aa9914b5f04d062469d50100111eb9c9c tag=v1.0 root=. narHash=sha256-abc= vendor=true entry=src/lib.bend\n" ++
    "deps|bend-tensors hash=0x39d8166231e68361eb37e8bef9287b8a hub=bend-tensors@0.0.0.2 entry=tensors.bend\n" ++
    "tools|bolt git=https://github.com/Emerging-Patterns/bolt rev=38da7d930a9251f44cf7434032e954b2e706564b tag=v1.7.0 root=. narHash=sha256-def=\n"

# the sections the lock above holds, as eztoml v0.1.0 read them
def old.lock.sects() -> String:
    "bad=\n" ++
    "lock version=2 hub=https://hub.bend-lang.com\n" ++
    "packages|0x7e63a5b990a375c304ed462c071214a6|source kind=git url=https://github.com/owner/repo rev=16773c0aa9914b5f04d062469d50100111eb9c9c entry=src/lib.bend root=. narHash=sha256-abc= tag=v1.0\n" ++
    "packages|0x7e63a5b990a375c304ed462c071214a6|files LICENSE=309f5aae946e4db157750e002fb179a74ed0fe27fce09a7be68a6977b14f205f src/lib.bend=fff16a9f901df7150ec13b5488820e8fe4ca288133c3cf2e4fcc04ec6a3671f9\n" ++
    "names bend-tensors@0.0.0.2=0x39d8166231e68361eb37e8bef9287b8a\n" ++
    "tools|bolt git=https://github.com/Emerging-Patterns/bolt rev=38da7d930a9251f44cf7434032e954b2e706564b root=. narHash=sha256-def=\n"

def main() -> IO(Unit):
  do IO<Unit>:
    +led : String <- IO.pure(String, Rend.render(M.parse(old.ledger())))
    Check.eq_str("an old ledger reads", Bool.show(String.contains(M.show(M.parse(old.ledger())), "error")), "False")
    Check.eq_str("to the model its new form reads to", M.show(M.parse(old.ledger())),
      M.show(M.parse(led)))
    Check.eq_str("to the sections eztoml v0.1.0 read", read(old.ledger()), old.ledger.sects())
    Check.eq_str("and to the sections its new form reads to", read(old.ledger()), read(led))
    Check.eq_str("and is written in the new form", led, new.ledger())
    +lock : String <- IO.pure(String, T.normal(old.lock()))
    Check.eq_str("an old lock reads to the sections eztoml v0.1.0 read", read(old.lock()),
      old.lock.sects())
    Check.eq_str("and to the sections its new form reads to",
      read(old.lock()), read(lock))
    Check.eq_str("and is written in the new form", lock, new.lock())
    Check.eq_str("the new form is written again as itself", T.normal(lock), lock)

#|ok an old ledger reads
#|ok to the model its new form reads to
#|ok to the sections eztoml v0.1.0 read
#|ok and to the sections its new form reads to
#|ok and is written in the new form
#|ok an old lock reads to the sections eztoml v0.1.0 read
#|ok and to the sections its new form reads to
#|ok and is written in the new form
#|ok the new form is written again as itself

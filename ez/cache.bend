# ez/cache: a lane not run twice over the same evidence. A lane's answer is a
# function of what it reads — each test, every module those reach through a
# relative import, the foreign C and JS bodies beside them, and the toolchain
# that would compile them — so a key over exactly that says whether the run can
# be skipped. The walk is `pkg/pkg.bend`, which is the one `bend --publish`
# uses and already hashes every file it finds; the aggregate is the entry, so
# the test list and every trailer are inside the key too.
#
# The rule that keeps a cache honest: a key is written only when every test of
# the lane held, and read only as a pass. A cache that went green on stale
# evidence would be worse than no cache at all, and `--full` ignores it.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ../pkg/pkg.bend as K
import ../sha/sha.bend as Sha
import ./env.bend as Env

# the toolchain a key is over. A new bend checks and emits differently, and the
# native lane hands its C to whatever `$CC` names, so both belong in the key.
def tool() -> IO(String):
  do IO<String>:
    +out : String <- R.exec(["bend", "--version"])
    +cc : String <- Env.var("CC", "cc")
    return String.trim(R.text(out)) ++ " " ++ cc

# what a lane's answer depends on, as one name: the toolchain, the lane, and
# the package hash over every file the entry reaches, each by its sha256
def key(+lane: String, +tool: String, +entry: String) -> IO(String):
  do IO<String>:
    p : K.Pkg <- K.pkg_of(entry)
    return lane ++ "-" ++ String.take(Sha.hex(tool ++ " " ++ K.pkg.hash(p)), 32n)

# a key, but only for a lane that is going to run at all: the walk behind one
# reads every file the lane would, and a lane that is skipped should not pay it
def key.on(on: Bool, +lane: String, +tool: String, +entry: String) -> IO(String):
  match on:
    case False{}:
      IO.pure(String, "")
    case True{}:
      key(lane, tool, entry)

# where a lane's answer is remembered
def at(+k: String) -> String:
  ".gate/cache/" ++ k

# whether a file is there
def there(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{_s}:
      True{}

# whether this lane has already held over exactly this evidence
def fresh(on: Bool, +k: String) -> IO(Bool):
  match on:
    case False{}:
      IO.pure(Bool, False{})
    case True{}:
      do IO<Bool>:
        m : Maybe<&2, String> <- F.read(at(k))
        return there(m)

# a lane's answer remembered, and only when every test of it held
def keep(ok: Bool, +k: String, +what: String) -> IO(Unit):
  match ok:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      do IO<Unit>:
        _w : Bool <- F.write(at(k), what ++ "\n")
        return Unit{}

# the directory the answers are kept in
def make() -> IO(Unit):
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", ".gate/cache"])
    return Unit{}

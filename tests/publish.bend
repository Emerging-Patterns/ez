# ez's package hash, pinned against bend itself. A real `bend --publish` runs
# against a local hub, and the hash it mines must equal the one ez computes
# without publishing anything. If bend's packaging ever changes, this fails
# instead of the two hashes quietly drifting apart.
#
# The hub is check/oracle.bend, never the real one. `bend --publish` uploads,
# and uploading someone's tree to a public hub is not a thing a test does.
import Base
import ../run/run.bend as R
import ../io/file.bend as F
import ../ez/quiet.bend as Q
import ../check/kit.bend as Check
import ../check/world.bend as W

# the repo being published: a nested layout with an import across it, which is
# the shape that makes the file walk worth checking
def repo(+at: String) -> IO(Unit):
  do IO<Unit>:
    W.mkdir(at ++ "/src/util")
    _m : Bool <- F.write(at ++ "/src/util/math.bend",
      "import Base\n\n# double the number\ndef double(+x: U32) -> U32:\n" ++
      "  (x * 2 : U32)\n")
    _l : Bool <- F.write(at ++ "/src/lib.bend",
      "import Base\nimport ./util/math.bend as M\n\n" ++
      "# four times the number\ndef quad(+x: U32) -> U32:\n" ++
      "  M.double(M.double(x))\n")
    return Unit{}

# what ez says a file's package would be, without publishing it: the hash on
# the first line, the directory its paths are written from on the second, then
# the manifest. One run answers both questions, because a second `bend` over
# `pkg/main.bend` would cost a whole check to learn nothing new. The check
# report shares the stream with the answer, so the caller takes it back out.
def ours(+here: String, +entry: String) -> IO(String):
  R.exec(["env", "BEND_LIB=" ++ here ++ "/.ez/lib", "EZ_ENTRY=" ++ entry,
    "bend", here ++ "/pkg/main.bend"])

# the hash `bend --publish` mined, which is the line of its output that names a
# package: the proof of work reports as it goes, on the same stream.
def theirs(+repo: String, +port: String) -> IO(String):
  do IO<String>:
    +out : String <- R.exec(W.inside(repo, ["env",
      "BEND_HUB=http://127.0.0.1:" ++ port, "bend", "src/lib.bend",
      "--publish"]))
    return W.starting(String.lines(R.text(out)), "0x")

# the two hashes, and then the two manifests the hashes are taken over. The
# manifests are compared with their trailing blank dropped from both sides:
# the hash above is the digest of the manifest text, so its equality already
# pins the bytes, and this second check is here to say which line differs when
# the first one fails.
def compare(+here: String, +root: String, +port: String) -> IO(Unit):
  do IO<Unit>:
    +got : String <- theirs(root ++ "/repo", port)
    +out : String <- ours(here, root ++ "/repo/src/lib.bend")
    +said : List<&2, String> <- IO.pure(List<&2, String>,
      String.lines(Q.filter(R.text(out))))
    Check.eq_str("ez computes the hash bend publishes", W.nth(said, 0n), got)
    +man : Maybe<&2, String> <- F.read(root ++ "/hub/" ++ got ++ "/manifest")
    Check.eq_str("ez computes the manifest bend publishes",
      Q.chomp(String.join(List.drop(&2, String, said, 2n), "\n")),
      Q.chomp(F.text_of(man)))

# everything, once the scratch directory and the port are known
def go(+here: String, +root: String, +port: String) -> IO(Unit):
  do IO<Unit>:
    repo(root ++ "/repo")
    W.mkdir(root ++ "/hub")
    +pid : String <- W.spawn(["env", "BEND_LIB=" ++ here ++ "/.ez/lib",
      "bend", here ++ "/check/oracle.bend", root ++ "/hub", port])
    up : Bool <- W.ready(["curl", "-fsS", "--max-time", "5",
      "http://127.0.0.1:" ++ port ++ "/"])
    Check.eq_str("the oracle answers",
      Bool.pick(String, up, "yes", "no"), "yes")
    compare(here, root, port)
    W.stop(pid)
    W.rm(root)

def main() -> IO(Unit):
  do IO<Unit>:
    here : String <- W.here()
    root : String <- W.tmp()
    port : String <- W.port()
    go(here, root, port)

#|ok the oracle answers
#|ok ez computes the hash bend publishes
#|ok ez computes the manifest bend publishes

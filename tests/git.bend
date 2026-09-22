# A Bend repo that was never published, depended on anyway. ez computes the
# `0x` name `bend --publish` would have given the tree, vendors it under that
# name, and nix rebuilds the same tree from the pinned rev alone. The two trees
# are compared file by file, because the claim is that they are the same
# package and not merely two packages that both work.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../ez/quiet.bend as Q
import ../check/kit.bend as Check
import ../check/world.bend as W

# a check whose answer is a yes or a no
def yes(name: String, ok: Bool) -> IO(Unit):
  Check.eq_str(name, Bool.pick(String, ok, "yes", "no"), "yes")

# what a program answered, with bend's check report taken out of it
def answer(+out: String) -> String:
  W.last(String.lines(Q.filter(R.text(out))))

# the upstream repo: two files, one importing the other, committed, tagged and
# never published
def upstream(+at: String) -> IO(String):
  do IO<String>:
    W.mkdir(at ++ "/src/util")
    _m : Bool <- F.write(at ++ "/src/util/math.bend",
      "import Base\n\n# double the number\ndef double(+x: U32) -> U32:\n" ++
      "  (x * 2 : U32)\n")
    _l : Bool <- F.write(at ++ "/src/lib.bend",
      "import Base\nimport ./util/math.bend as M\n\n" ++
      "# four times the number\ndef quad(+x: U32) -> U32:\n" ++
      "  M.double(M.double(x))\n")
    _i : String <- R.exec(["git", "-C", at, "init", "-q"])
    _a : String <- R.exec(["git", "-C", at, "add", "-A"])
    _c : String <- R.exec(["git", "-C", at, "-c", "user.email=t@t",
      "-c", "user.name=t", "commit", "-q", "-m", "init"])
    _g : String <- R.exec(["git", "-C", at, "-c", "user.email=t@t",
      "-c", "user.name=t", "tag", "-a", "v1.0", "-m", "v1.0"])
    +rev : String <- R.exec(["git", "-C", at, "rev-parse", "HEAD"])
    return W.line(rev)

# that repo served over the protocol, so the nix sandbox can reach it too. The
# annotated tag is pushed as well, since the peeled `^{}` row is the one that
# has to be pinned.
def serve(+at: String, +port: String) -> IO(String):
  do IO<String>:
    W.mkdir(at ++ "/srv")
    _c : String <- R.exec(["git", "clone", "-q", "--bare", at ++ "/upstream",
      at ++ "/srv/upstream.git"])
    _a : String <- R.exec(["git", "-C", at ++ "/srv/upstream.git", "config",
      "uploadpack.allowAnySHA1InWant", "true"])
    _t : String <- R.exec(["git", "-C", at ++ "/srv/upstream.git", "config",
      "uploadpack.allowTipSHA1InWant", "true"])
    _p : String <- R.exec(["git", "-C", at ++ "/upstream", "push", "-q",
      at ++ "/srv/upstream.git", "v1.0"])
    pid : String <- W.spawn(["git", "daemon", "--reuseaddr",
      "--listen=127.0.0.1", "--port=" ++ port, "--base-path=" ++ at ++ "/srv",
      "--export-all"])
    up : Bool <- W.ready(["git", "ls-remote",
      "git://127.0.0.1:" ++ port ++ "/upstream.git"])
    yes("the upstream remote answers", up)
    return pid

# the repo vendored under the name it would have been published as, by rev and
# then by tag, which must come out as the same package. The second vendoring
# goes into a BEND_LIB of its own, so the two trees can be compared file by
# file rather than one of them overwriting the other.
def vendor(+repo: String, +app: String, +url: String, +rev: String) -> IO(String):
  do IO<String>:
    _i : String <- R.exec(W.ez(repo, app, ["init", "myapp", "main.bend"]))
    +out : String <- R.exec(W.ez(repo, app, ["add", url, rev, "src/lib.bend"]))
    +led : Maybe<&2, String> <- F.read(app ++ "/ez.toml")
    +hash : String <- IO.pure(String, W.value(F.text_of(led), "hash"))
    Check.eq_str("add says the import line the package is reachable by",
      W.containing(String.lines(R.text(out)), "import "),
      "import " ++ hash ++ "/lib.bend as Lib")
    +tag : String <- R.exec(W.inside(app, ["env",
      "BEND_LIB=" ++ app ++ "/.ez/tag", repo ++ "/bin/ez.bin", "add", url,
      "v1.0", "src/lib.bend"]))
    Check.eq_str("the tag it resolved through is written down",
      W.containing(String.lines(R.text(tag)), " is "), "v1.0 is " ++ rev)
    +same : String <- R.exec(["diff", "-r", app ++ "/.ez/lib/" ++ hash,
      app ++ "/.ez/tag/" ++ hash])
    yes("a tag vendors the same package as its commit", R.ok(same))
    +ats : String <- W.only(app ++ "/.ez", "origins.*")
    +org : Maybe<&2, String> <- F.read(ats)
    yes("the lock keeps the tag beside the rev",
      String.contains(
        W.containing(String.lines(F.text_of(org)), "tag"), "v1.0"))
    return hash

# the vendored package built with no hub at all, and the lock that records
# where it came from
def local(+repo: String, +app: String, +hash: String, +rev: String) -> IO(Unit):
  do IO<Unit>:
    _w : Bool <- F.write(app ++ "/main.bend",
      "import Base\nimport " ++ hash ++ "/lib.bend as Lib\n\n" ++
      "def main() -> U32:\n  Lib.quad(11)\n")
    W.track(app)
    +out : String <- R.exec(W.inside(app, ["env", "BEND_HUB=http://127.0.0.1:1",
      "BEND_LIB=" ++ app ++ "/.ez/lib", "bend", "main.bend"]))
    Check.eq_str("the vendored package builds, with no hub at all",
      answer(out), "44")
    _lk : String <- R.exec(W.ez(repo, app, ["lock"]))
    +at : String <- W.only(app, "ez.lock.*")
    +txt : Maybe<&2, String> <- F.read(at)
    yes("the lock records the git rev, not the hub",
      Bool.and(String.contains(F.text_of(txt), "git"),
        String.contains(F.text_of(txt), rev)))

# nix rebuilding the package from the rev alone. The store path is the last
# line of the build that names one, since the build's log shares the stream.
def rebuild(+repo: String, +app: String, +hash: String) -> IO(Unit):
  do IO<Unit>:
    +lock : String <- W.only(app, "ez.lock.*")
    _n : Bool <- F.write(app ++ "/build.nix",
      "let pkgs = import <nixpkgs> { };\nin pkgs.callPackage " ++ repo ++
      "/nix/bend-lib.nix { } " ++ lock ++ "\n")
    +out : String <- R.exec(["nix-build", "--no-out-link", app ++ "/build.nix"])
    +at : String <- IO.pure(String,
      W.starting.last(String.lines(R.text(out)), "/nix/store/", ""))
    +same : String <- R.exec(["diff", "-r", app ++ "/.ez/lib/" ++ hash,
      at ++ "/" ++ hash])
    yes("nix rebuilds the package byte for byte", R.ok(same))
    +ran : String <- R.exec(W.inside(app, ["env", "BEND_HUB=http://127.0.0.1:1",
      "BEND_LIB=" ++ at, "bend", "main.bend"]))
    Check.eq_str("the nix tree builds with no hub", answer(ran), "44")

# everything, once the scratch directory and the port are known
def go(+repo: String, +root: String, +port: String) -> IO(Unit):
  do IO<Unit>:
    +rev : String <- upstream(root ++ "/upstream")
    +pid : String <- serve(root, port)
    W.mkdir(root ++ "/app")
    +hash : String <- vendor(repo, root ++ "/app",
      "git://127.0.0.1:" ++ port ++ "/upstream.git", rev)
    local(repo, root ++ "/app", hash, rev)
    rebuild(repo, root ++ "/app", hash)
    W.stop(pid)
    W.rm(root)

def main() -> IO(Unit):
  do IO<Unit>:
    repo : String <- W.here()
    root : String <- W.tmp()
    port : String <- W.port()
    go(repo, root, port)

#|ok the upstream remote answers
#|ok add says the import line the package is reachable by
#|ok the tag it resolved through is written down
#|ok a tag vendors the same package as its commit
#|ok the lock keeps the tag beside the rev
#|ok the vendored package builds, with no hub at all
#|ok the lock records the git rev, not the hub
#|ok nix rebuilds the package byte for byte
#|ok the nix tree builds with no hub

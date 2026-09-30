# git/fetch: the git commands the interpreter runs. What a printed answer
# means lives in git/git.bend, which the proofs import. These run a program.
import Base
import 0xabe575924687afad4cee1a2c1194d639/main.bend as R
import ../pkg/path.bend as P
import ../sha/dump.bend as Dump
import ../share/say.bend as Say
import ../share/spin.bend as Spin
import ./git.bend as Git

# a git command that failed stops the command, with whatever git said
def ran(ok: Bool, what: String, text: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: git " ++ what ++ ": " ++ text)

# one git command
def run(what: String, args: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +out : String <- R.exec(args)
    ran(R.ok(out), what, R.text(out))

# a source as git is to read it. A ledger records a local path as it was
# given, relative to the project, which is the directory ez runs in, so the
# ledger reads the same on every clone. git reads such a path from somewhere
# else: a fetch from inside its work directory, and `ls-remote` from the top
# of any repository around it. Every git command here that is handed a source
# is handed this instead.
def anchored(+url: String) -> IO(String):
  do IO<String>:
    +here : String <- R.exec(["pwd"])
    return P.anchor(String.trim(R.text(here)), url)

# the checkout a package is taken from: the pinned commit alone, at the depth
# of one, so a repo with a long history costs nothing to vendor. The fetch is
# quiet; the line above it is what a person sees while it runs.
def clone.say(+work: String, +url: String, +rev: String, +msg: String) -> IO(Unit):
  do IO<Unit>:
    +s : Say.Spin <- Spin.hold(msg)
    +from : String <- anchored(url)
    run("init", ["git", "init", "-q", work])
    run("fetch", ["git", "-C", work, "fetch", "-q", "--depth", "1", from, rev])
    run("checkout", ["git", "-C", work, "checkout", "-q", rev])
    Spin.done(s)

# a shallow clone of one commit into `work`, with a line saying what it fetches
def clone(+work: String, +url: String, +rev: String) -> IO(Unit):
  clone.say(work, url, rev, Say.git.fetch(url))


# the NAR hash nix rebuilds the checkout by. `fetchgit` hashes the working
# tree with its `.git` taken off, so that is what is weighed here and the
# caller strips `.git` before asking. Computed in Bend; nix is not required.
def nar(+work: String) -> IO(String):
  Dump.path(work)

# the NAR hash of one commit. The checkout is weighed the way `fetchgit`
# weighs it, then removed. Nothing is laid under BEND_LIB.
def weigh(+url: String, +rev: String) -> IO(String):
  +work = ".ez/weigh-" ++ rev
  do IO<String>:
    _rm : String <- R.exec(["rm", "-rf", work])
    _mk : String <- R.exec(["mkdir", "-p", work])
    clone(work, url, rev)
    _dg : String <- R.exec(["rm", "-rf", work ++ "/.git"])
    +s : Say.Spin <- Spin.hold(Say.hashing(rev))
    +nh : String <- nar(work)
    Spin.done(s)
    _cl : String <- R.exec(["rm", "-rf", work])
    return nh


# a remote with no HEAD is not a repo an upgrade can move
def remote.got(empty: Bool, +rev: String, +branch: String, +url: String) -> IO(Git.Tip):
  match empty:
    case True{}:
      IO.die(Git.Tip, 1, "ez: " ++ url ++ " has no HEAD")
    case False{}:
      IO.pure(Git.Tip, Git.Tip{rev, branch})

# what ls-remote said, or why it said nothing
def remote.said(ok: Bool, +url: String, +text: String) -> IO(Git.Tip):
  match ok:
    case False{}:
      IO.die(Git.Tip, 1, "ez: git ls-remote " ++ url ++ ": " ++ text)
    case True{}:
      +rs = Git.rows(String.lines(text))
      remote.got(String.is_empty(Git.tip.rev(rs)), Git.tip.rev(rs), Git.tip.branch(rs), url)

# HEAD on the remote: the commit the default branch tips, and that branch's
# name. `--symref` is what puts the branch on the line in front of the commit.
def remote(+url: String) -> IO(Git.Tip):
  do IO<Git.Tip>:
    +from : String <- anchored(url)
    +out : String <- R.exec(["git", "ls-remote", "--symref", from, "HEAD"])
    remote.said(R.ok(out), url, R.text(out))

# a bare clone, blobs left behind. Ancestry only needs the commits. The clone
# is quiet; the line is what shows while it runs.
def clone.bare(+work: String, +url: String) -> IO(Unit):
  do IO<Unit>:
    +s : Say.Spin <- Spin.hold(Say.git.fetch(url))
    +from : String <- anchored(url)
    run("clone", ["git", "clone", "--bare", "--filter=blob:none", "-q", from, work])
    Spin.done(s)

# merge-base answers 0 for a descendant, 1 for anything else, and some other
# status when the question itself could not be asked
def descendant.no(no: Bool, +text: String) -> IO(Bool):
  match no:
    case True{}:
      IO.pure(Bool, False{})
    case False{}:
      IO.die(Bool, 1, "ez: git merge-base: " ++ text)

# the status, read
def descendant.pick(yes: Bool, no: Bool, text: String) -> IO(Bool):
  match yes:
    case True{}:
      IO.pure(Bool, True{})
    case False{}:
      descendant.no(no, text)

# the status a merge-base answered with
def descendant.code(+code: String, +text: String) -> IO(Bool):
  descendant.pick(String.eq(code, "0"), String.eq(code, "1"), text)

# the clone, the question, the clone gone. The same commit is a descendant
# of itself and needs no clone to say so.
def descendant.clone(+work: String, +url: String, +pin: String, +tip: String) -> IO(Bool):
  do IO<Bool>:
    _rm : String <- R.exec(["rm", "-rf", work])
    clone.bare(work, url)
    +out : String <- R.exec(["git", "-C", work, "merge-base", "--is-ancestor",
      pin, tip])
    _cl : String <- R.exec(["rm", "-rf", work])
    descendant.code(R.code(out), R.text(out))

# whether `tip` descends from `pin`, the same commit included
def descendant.go(same: Bool, work: String, url: String, pin: String, tip: String) -> IO(Bool):
  match same:
    case True{}:
      IO.pure(Bool, True{})
    case False{}:
      descendant.clone(work, url, pin, tip)

# whether `tip` descends from `pin`. `work` is a directory the clone may use.
def descendant.at(+work: String, +url: String, +pin: String, +tip: String) -> IO(Bool):
  descendant.go(String.eq(pin, tip), work, url, pin, tip)


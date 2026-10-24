# ws/run: the interpreter's half of workspaces. It reads what the root search
# asks for (ws/root.bend) and runs the hop ws/hop.bend decides, and for `ez
# lock` it reads every ez.toml git lists under a workspace root so that
# ws/joint.bend can join them. It decides nothing: where the root is, whether
# to run again there, which ledgers are members and what the lock is planned
# from are the pure modules'. That it reads and runs faithfully is
# EZ-TRUST-2. It runs programs, so no law imports it.
import Base
import 0xead4c7939c9eaca8d47da53b4496b731/main.bend as Sn
import ../io/file.bend as F
import ../share/args.bend as Args
import ../share/pass.bend as Pass
import ../ledger/render.bend as Rend
import ./workspace.bend as W
import ./root.bend as R
import ./hop.bend as H
import ./joint.bend as J

# what the search found, and the top of the checkout it searched from
type Searched is Data:
  Searched{top: String, found: R.Found}

# a directory's ez.toml, from the top of the checkout
def ledger.path(+top: String, ds: List<&2, String>) -> String:
  top ++ "/" ++ W.segs.text(List.append(&2, String, ds, ["ez.toml"]))

# the ez.toml of every directory the search asks about, nearest first
def read.ups(+top: String, asks: List<&2, R.Ask>) -> IO(List<&2, R.Up>):
  match asks:
    case []:
      IO.pure(List<&2, R.Up>, [])
    case R.Ask{+ds, rs} <> tl:
      do IO<List<&2, R.Up>>:
        tx : Maybe<&2, String> <- F.read(ledger.path(top, ds))
        rest : List<&2, R.Up> <- read.ups(top, tl)
        return R.Up{ds, rs, tx} <> rest

# the search, once git said where ez runs. Outside a checkout there is no
# committed ledger above, so no workspace: the directory is its own project.
def search.at(here: Maybe<&2, List<&2, String>>, +top: String) -> IO(Searched):
  match here:
    case None{}:
      IO.pure(Searched, Searched{"", R.Alone{}})
    case Some{hs}:
      do IO<Searched>:
        ups : List<&2, R.Up> <- read.ups(top, R.asks(hs))
        return Searched{top, R.root.go(ups)}

# where ez runs, from what git printed, or nothing when git could not say
def here.git(ok: Bool, +text: String) -> Maybe<&2, List<&2, String>>:
  match ok:
    case True{}:
      R.here.of(String.trim(text))
    case False{}:
      None{}

# the search for the root, from where ez runs up to the top of its checkout
def search() -> IO(Searched):
  do IO<Searched>:
    +pre : String <- Sn.exec(["git", "rev-parse", "--show-prefix"])
    +top : String <- Sn.exec(["git", "rev-parse", "--show-toplevel"])
    search.at(here.git(Bool.and(Sn.ok(pre), Sn.ok(top)), Sn.text(pre)), String.trim(Sn.text(top)))

# the program's own name, and every word after it
def argv() -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    xs : List<&1, String> <- IO.args()
    return Args.copy(xs)

# the same words run again at the root
def hop.go(+dir: String, +pwd: String, xs: List<&2, String>) -> IO(U32):
  match xs:
    case []:
      IO.pure(U32, 1)
    case +prog <> rest:
      Pass.run(H.line(dir, pwd, prog, rest))

# the hop's status, as this command's
def hop.end(zero: Bool, +code: U32) -> IO(Unit):
  match zero:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.exit(code)

# a run at the root, which ends as that run ended
def hop.run(+dir: String) -> IO(Unit):
  do IO<Unit>:
    +pwd : String <- Sn.exec(["pwd"])
    xs : List<&2, String> <- argv()
    +code : U32 <- hop.go(dir, String.trim(Sn.text(pwd)), xs)
    hop.end(U32.is_eq(code, 0), code)

# a command acted on as its hop says
def hop.at(hop: H.Hop, go: Unit -> IO(Unit)) -> IO(Unit):
  match hop:
    case H.Here{}:
      go(Unit{})
    case H.Stop{why}:
      IO.die(Unit, 1, why)
    case H.Hop{dir}:
      hop.run(dir)

# what the search found, acted on
def at.searched(st: Searched, go: Unit -> IO(Unit)) -> IO(Unit):
  Searched{+top, found} = st
  hop.at(H.hop(top, found), go)

# a whole-workspace command, `ez lock`, `ez fetch` or `ez doctor`: run where
# it is when that is its project's root, and again at the root when it is run
# in a member
def at.root(go: Unit -> IO(Unit)) -> IO(Unit):
  do IO<Unit>:
    st : Searched <- search()
    at.searched(st, go)

# ---------------------------------------------------------------------------
# the ledger `ez lock` is planned from

# every listed ez.toml, read
def read.found(ps: List<&2, String>) -> IO(List<&2, J.Found>):
  match ps:
    case []:
      IO.pure(List<&2, J.Found>, [])
    case +hd <> tl:
      do IO<List<&2, J.Found>>:
        mm : Maybe<&2, String> <- F.read(hd)
        rest : List<&2, J.Found> <- read.found(tl)
        return J.Found{hd, F.text_of(mm)} <> rest

# the non-empty lines
def lines(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case []:
      []
    case +hd <> tl:
      +more = lines(tl)
      Bool.pick(List<&2, String>, String.is_empty(hd), more, hd <> more)

# the joint ledger, as the lock reads it, or the refusal that leaves none
def joint.at(jj: J.Joint, +own: Maybe<&2, String>) -> IO(Maybe<&2, String>):
  match jj:
    case J.Lone{}:
      IO.pure(Maybe<&2, String>, own)
    case J.Clash{why}:
      IO.die(Maybe<&2, String>, 1, why)
    case J.Joint{mm}:
      IO.pure(Maybe<&2, String>, Some{Rend.show(mm)})

# a workspace root's ledger joined with every member's, once git listed them
def joint.listed(ok: Bool, +text: String, +out: String) -> IO(Maybe<&2, String>):
  match ok:
    case True{}:
      do IO<Maybe<&2, String>>:
        fs : List<&2, J.Found> <- read.found(lines(String.lines(out)))
        joint.at(J.joint(text, fs), Some{text})
    case False{}:
      IO.die(Maybe<&2, String>, 1,
        "ez: a workspace is locked from the ez.toml files git tracks, and git could not list them: " ++
          String.trim(out))

# a workspace root's ledger joined with every member's. An upgrade writes back
# the ledger it was planned from, and a workspace's pins live in its members'
# ledgers, so `ez lock --upgrade` at a workspace root is refused until it
# moves them there.
def joint.go(up: Bool, +text: String) -> IO(Maybe<&2, String>):
  match up:
    case True{}:
      IO.die(Maybe<&2, String>, 1,
        "ez: ez lock --upgrade does not move a workspace's pins yet; run it in a project of its own")
    case False{}:
      do IO<Maybe<&2, String>>:
        +out : String <- Sn.exec(["git", "-c", "core.quotepath=off", "ls-files", "--",
          ":(glob)**/ez.toml"])
        joint.listed(Sn.ok(out), text, Sn.text(out))

# what one ledger's text says: no workspace, read as it is, or a workspace
# root, whose members are read and joined
def joint.read(rd: W.Read, up: Bool, +text: String) -> IO(Maybe<&2, String>):
  match rd:
    case W.Lone{}:
      IO.pure(Maybe<&2, String>, Some{text})
    case _:
      joint.go(up, text)

# the ledger `ez lock` is planned from: ez.toml as it is, or, at a workspace
# root, the joint ledger of the root and every member
def ledger(led: Maybe<&2, String>, up: Bool) -> IO(Maybe<&2, String>):
  match led:
    case None{}:
      IO.pure(Maybe<&2, String>, None{})
    case Some{+text}:
      joint.read(W.spec.of(text), up, text)

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
import ./up.bend as U
import ./pin.bend as Pin
import ../ledger/manifest.bend as M
import ../pkg/path.bend as P
import ../pkg/pkg.bend as K
import ../lock/world.bend as LW

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

# the ledger `ez lock` is planned from, what an upgrade needs to write its
# pins back, and the answers the lock reads the workspace's members from
type Planned is Data:
  Planned{ledger: Maybe<&2, String>, back: U.Back, seeds: List<&2, LW.Reply>}

# the joint ledger, as the lock reads it, or the refusal that leaves none
def joint.at(
  jj: J.Joint,
  +text: String,
  +spec: W.Spec,
  +fs: List<&2, J.Found>,
  +files: List<&2, K.Source>,
  +lock: String
) -> IO(Planned):
  match jj:
    case J.Lone{}:
      IO.pure(Planned, Planned{Some{text}, U.Alone{}, []})
    case J.Clash{why}:
      IO.die(Planned, 1, why)
    case J.Joint{+mm}:
      IO.pure(Planned, Planned{Some{Rend.show(mm)}, U.Back{text, spec, fs, lock},
        J.seeds(J.Joint{mm}, files)})

# a workspace root's ledger joined with every member's, once git listed them
def joint.listed(
  ok: Bool,
  +text: String,
  +spec: W.Spec,
  +out: String,
  +files: List<&2, K.Source>
) -> IO(Planned):
  match ok:
    case True{}:
      do IO<Planned>:
        +fs : List<&2, J.Found> <- read.found(lines(String.lines(out)))
        lk : Maybe<&2, String> <- F.read("ez.lock.toml")
        joint.at(J.joint(text, fs, files), text, spec, fs, files, F.text_of(lk))
    case False{}:
      IO.die(Planned, 1,
        "ez: a workspace is locked from the ez.toml files git tracks, and git could not list them: " ++
          String.trim(out))

# a workspace root's ledger joined with every member's
def joint.go(+text: String, +spec: W.Spec, +files: List<&2, K.Source>) -> IO(Planned):
  do IO<Planned>:
    +out : String <- Sn.exec(["git", "-c", "core.quotepath=off", "ls-files", "--", ":(glob)**/ez.toml"])
    joint.listed(Sn.ok(out), text, spec, Sn.text(out), files)

# what one ledger's text says: no workspace, read as it is; a workspace root,
# whose members are read and joined; or a table that cannot be read, which
# the joint ledger refuses
def joint.read(rd: W.Read, +text: String, +files: List<&2, K.Source>) -> IO(Planned):
  match rd:
    case W.Lone{}:
      IO.pure(Planned, Planned{Some{text}, U.Alone{}, []})
    case W.Bad{why}:
      IO.die(Planned, 1, why)
    case W.Root{+spec}:
      joint.go(text, spec, files)

# the ledger `ez lock` is planned from: ez.toml as it is, or, at a workspace
# root, the joint ledger of the root and every member. `files` are the
# committed `.bend` files, which a member's package is walked over.
def ledger(led: Maybe<&2, String>, +files: List<&2, K.Source>) -> IO(Planned):
  match led:
    case None{}:
      IO.pure(Planned, Planned{None{}, U.Alone{}, []})
    case Some{+text}:
      joint.read(W.spec.of(text), text, files)

# ---------------------------------------------------------------------------
# a member's own commands

# an environment variable's text; unset, ""
def env.text(rr: Result<&1, &1, U32 & String, String>) -> String:
  match rr:
    case Fail{_e}:
      ""
    case Done{ss}:
      String.trim(ss)

# BEND_LIB as the environment has it, "" for unset
def env.lib() -> IO(String):
  do IO<String>:
    rr : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_LIB")
    return env.text(rr)

# the same words run again where they are, with BEND_LIB set
def lib.go(+at: String, +pwd: String, xs: List<&2, String>) -> IO(U32):
  match xs:
    case []:
      IO.pure(U32, 1)
    case +prog <> rest:
      Pass.run(H.lib.line(at, pwd, prog, rest))

# a command acted on as the library decision says: where it is, or again
# where it is with BEND_LIB set to the root's
def lib.at(lib: H.Lib, go: Unit -> IO(Unit)) -> IO(Unit):
  match lib:
    case H.Keep{}:
      go(Unit{})
    case H.Set{+at}:
      do IO<Unit>:
        +pwd : String <- Sn.exec(["pwd"])
        xs : List<&2, String> <- argv()
        +code : U32 <- lib.go(at, String.trim(Sn.text(pwd)), xs)
        hop.end(U32.is_eq(code, 0), code)

# what the search found, acted on for a member's own command
def in.searched(st: Searched, +env: String, go: Unit -> IO(Unit)) -> IO(Unit):
  Searched{+top, found} = st
  lib.at(H.lib(top, found, env), go)

# a command that acts on a member's own ledger and entry, `ez add`, `ez
# remove`, `ez check`, `ez build`, `ez run` and `ez publish`: run where it is,
# with the root's library when it is run in a member
def in.member(go: Unit -> IO(Unit)) -> IO(Unit):
  do IO<Unit>:
    st : Searched <- search()
    +env : String <- env.lib()
    in.searched(st, env, go)

# every listed ez.toml under a directory, read
def read.under(+dir: String, ps: List<&2, String>) -> IO(List<&2, J.Found>):
  match ps:
    case []:
      IO.pure(List<&2, J.Found>, [])
    case +hd <> tl:
      do IO<List<&2, J.Found>>:
        mm : Maybe<&2, String> <- F.read(dir ++ "/" ++ hd)
        rest : List<&2, J.Found> <- read.under(dir, tl)
        return J.Found{hd, F.text_of(mm)} <> rest

# the joint ledger's dependencies, or none when it has none
def pins.joint(jj: J.Joint) -> List<&2, M.Dep>:
  match jj:
    case J.Joint{mm}:
      M.Manifest{_n, _e, _b, _h, _pa, _pv, ds, _ts} = mm
      ds
    case _:
      []

# every listed file under a directory, read, as the walk takes it
def files.under(+dir: String, ps: List<&2, String>) -> IO(List<&2, K.Source>):
  match ps:
    case []:
      IO.pure(List<&2, K.Source>, [])
    case +hd <> tl:
      do IO<List<&2, K.Source>>:
        mm : Maybe<&2, String> <- F.read(dir ++ "/" ++ hd)
        rest : List<&2, K.Source> <- files.under(dir, tl)
        return K.Source{hd, F.text_of(mm)} <> rest

# every dependency of the workspace a directory is in, as its root reads them
def pins.at(+dir: String) -> IO(List<&2, M.Dep>):
  do IO<List<&2, M.Dep>>:
    mm : Maybe<&2, String> <- F.read(dir ++ "/ez.toml")
    +out : String <- Sn.exec(["git", "-C", dir, "-c", "core.quotepath=off", "ls-files", "--",
      ":(glob)**/ez.toml"])
    fs : List<&2, J.Found> <- read.under(dir, lines(String.lines(Sn.text(out))))
    +bend : String <- Sn.exec(["git", "-C", dir, "-c", "core.quotepath=off", "ls-files", "--", "*.bend"])
    files : List<&2, K.Source> <- files.under(dir, lines(String.lines(Sn.text(bend))))
    return pins.joint(J.joint(F.text_of(mm), fs, files))

# the ref, once the workspace's pins are known
def ref.held(rr: Pin.Ref) -> IO(String):
  match rr:
    case Pin.Given{ref}:
      IO.pure(String, ref)
    case Pin.Held{why}:
      IO.die(String, 1, why)

# the ref an add goes on with, in what the search found
def ref.found(+top: String, found: R.Found, +home: String, +target: String, +ref: String) -> IO(String):
  match found:
    case R.Within{+root, +rel}:
      do IO<String>:
        +pins : List<&2, M.Dep> <- pins.at(P.join(top, W.segs.text(root)))
        ref.held(Pin.ref(pins, W.segs.text(rel), home, target, ref))
    case _:
      IO.pure(String, ref)

# and once the search was made
def add.searched(st: Searched, +home: String, +target: String, +ref: String) -> IO(String):
  Searched{+top, found} = st
  ref.found(top, found, home, target, ref)
# the ref `ez add <target> [ref]` goes on with: in a workspace, the pin the
# workspace already records for the source (EZ-WS-4)
def add.ref(+home: String, +target: String, +ref: String) -> IO(String):
  do IO<String>:
    st : Searched <- search()
    add.searched(st, home, target, ref)


# the lock, once the search was made
def lock.searched(st: Searched) -> String:
  Searched{+top, found} = st
  H.lock(top, found)

# the lock a member's own command reads: the root's, in a workspace
def lock.path() -> IO(String):
  do IO<String>:
    st : Searched <- search()
    return lock.searched(st)

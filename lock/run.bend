# lock/run: the interpreter for `ez lock`. It reads the ledger and the
# committed sources into a World, then loops: it asks the planner
# (lock/plan.bend) what is still open, answers each question by IO, and adds
# the answers to the World, until nothing is left to ask. Then it runs the
# planner's plan. It decides nothing: which packages to read, whether their
# bytes are the ones the ledger names, where an upgrade moves a pin, and what
# is written are the planner's. That it reads and executes faithfully is
# EZ-TRUST-2. Under `--upgrade` it also answers the upgrade's questions
# (lock/up.bend): what git prints for refs, the default branch and tags,
# ancestry, checkouts at a rev, the hub's manifest for a moved hash,
# `.gitignore`, and the project's sources. A new checkout's package is walked
# from its entry here, by `K.pkg_of`, which is interpreter code under
# EZ-TRUST-2 until `ez add` is converted.
import Base
import 0x9bfd9d57916f3439316c2775fd1f10b4/main.bend as R
import ../io/file.bend as F
import ../hub/hub.bend as Web
import ../git/git.bend as Git
import ../pkg/pkg.bend as K
import ../pkg/path.bend as P
import ../ez/say.bend as Say
import ./lock.bend as L
import ./world.bend as W
import ./up.bend as Up
import ./plan.bend as Plan

# ---------------------------------------------------------------------------
# the World's first fields

# an environment variable's text; unset, ""
def env.text(res: Result<&1, &1, U32 & String, String>) -> String:
  match res:
    case Fail{_e}:
      ""
    case Done{s}:
      s

# where packages live, which is with the project rather than in ~/.bend/lib
def lib.or(+dir: String) -> String:
  Bool.pick(String, String.is_empty(dir), ".ez/lib", dir)

# the BEND_LIB this project pins
def bend.lib() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, String> <- IO.get_env("BEND_LIB")
    return lib.or(String.trim(env.text(r)))

# the non-empty lines
def nonempty(ss: List<&2, String>) -> List<&2, String>:
  match ss:
    case []:
      []
    case +h <> t:
      +more = nonempty(t)
      Bool.pick(List<&2, String>, String.is_empty(h), more, h <> more)

# the ledger's text, or None when there is no ez.toml
def read.ledger() -> IO(Maybe<&2, String>):
  F.read("ez.toml")

# every listed path, read
def read.all(ps: List<&2, String>) -> IO(List<&2, W.Source>):
  match ps:
    case []:
      IO.pure(List<&2, W.Source>, [])
    case +h <> t:
      do IO<List<&2, W.Source>>:
        m : Maybe<&2, String> <- F.read(h)
        rest : List<&2, W.Source> <- read.all(t)
        return W.Source{h, F.text_of(m)} <> rest

# what git listed, or why it could not
def listed(ok: Bool, +text: String) -> IO(W.Listing):
  match ok:
    case True{}:
      do IO<W.Listing>:
        fs : List<&2, W.Source> <- read.all(nonempty(String.lines(text)))
        return W.Listed{fs}
    case False{}:
      IO.pure(W.Listing, W.Unlisted{
        "ez: ez lock reads the .bend files git tracks, and git could not list them: " ++
          String.trim(text)})

# every `.bend` file git tracks under the current directory, with its text.
# Untracked files are not a clone's, so they are not the lock's.
def read.listing() -> IO(W.Listing):
  do IO<W.Listing>:
    +out : String <- R.exec(["git", "-c", "core.quotepath=off", "ls-files",
      "--", "*.bend"])
    listed(R.ok(out), R.text(out))

# ---------------------------------------------------------------------------
# answering one question

# every text a fetch answered, or the first miss
def gots(+how: W.How, +manifest: String, gs: List<&2, Web.Got>, acc: List<&2, String>) -> W.Answer:
  match gs:
    case []:
      W.Got{how, manifest, List.reverse(&2, String, acc)}
    case g <> t:
      match g:
        case Web.Miss{why}:
          W.Miss{"ez: " ++ why}
        case Web.Have{body}:
          gots(how, manifest, t, body <> acc)

# every file of a hub package, fetched and checked against its sum
def hub.all(+hub: String, +hash: String, fs: List<&2, K.File>) -> IO(List<&2, Web.Got>):
  match fs:
    case []:
      IO.pure(List<&2, Web.Got>, [])
    case +h <> t:
      do IO<List<&2, Web.Got>>:
        g : Web.Got <- Web.fetch(L.url_of(hub, hash, K.file.at(h)), K.file.sum(h))
        rest : List<&2, Web.Got> <- hub.all(hub, hash, t)
        return g <> rest

# a hub package's files, once its manifest arrived
def hub.got(got: Web.Got, +hub: String, +hash: String) -> IO(W.Answer):
  match got:
    case Web.Miss{why}:
      IO.pure(W.Answer, W.Miss{why})
    case Web.Have{+body}:
      do IO<W.Answer>:
        gs : List<&2, Web.Got> <- hub.all(hub, hash, L.manifest.files(String.lines(body)))
        return gots(W.Served{}, body, gs, [])

# a hub package: its manifest, then every file it names
def answer.hub(+hub: String, +hash: String) -> IO(W.Answer):
  do IO<W.Answer>:
    +s : Say.Spin <- Say.hold(Say.dep.hub(hash))
    g : Web.Got <- Web.fetch(L.url_of(hub, hash, "manifest"), L.want(hash))
    a : W.Answer <- hub.got(g, hub, hash)
    Say.done(s)
    return a

# every file a tree's manifest names, read from beside it. A file that is not
# there reads as "", which does not hash to its sum.
def disk.all(+dir: String, fs: List<&2, K.File>) -> IO(List<&2, String>):
  match fs:
    case []:
      IO.pure(List<&2, String>, [])
    case +h <> t:
      do IO<List<&2, String>>:
        m : Maybe<&2, String> <- F.read(P.join(dir, K.file.at(h)))
        rest : List<&2, String> <- disk.all(dir, t)
        return F.text_of(m) <> rest

# a tree under BEND_LIB, as it is
def answer.lib(+dir: String, +manifest: String) -> IO(W.Answer):
  do IO<W.Answer>:
    ss : List<&2, String> <- disk.all(dir, L.manifest.files(String.lines(manifest)))
    return W.Got{W.Lib{}, manifest, ss}

# a checkout that could not be made or read is removed, and the question is
# answered with why
def clone.miss(+work: String, +why: String) -> IO(W.Answer):
  do IO<W.Answer>:
    _rm : String <- R.exec(["rm", "-rf", work])
    return W.Miss{why}

# a command of a clone that worked goes on with the clone; one that failed
# ends it
def clone.ran(ok: Bool, +work: String, +why: String, go: Unit -> IO(W.Answer)) -> IO(W.Answer):
  match ok:
    case True{}:
      go(Unit{})
    case False{}:
      clone.miss(work, why)

# one git command of a clone, and the rest of the clone when it worked
def clone.run(+work: String, what: String, args: List<&2, String>, go: Unit -> IO(W.Answer)) -> IO(W.Answer):
  do IO<W.Answer>:
    +out : String <- R.exec(args)
    clone.ran(R.ok(out), work, "ez: git " ++ what ++ ": " ++ R.text(out), go)

# the checkout's package, walked from its entry the way `ez add` walked it
def clone.walk(+work: String, +entry: String, +nar: String) -> IO(W.Answer):
  do IO<W.Answer>:
    +p : K.Pkg <- K.pkg_of(P.join(work, entry))
    +fs : List<&2, K.File> <- IO.pure(List<&2, K.File>, K.pkg.files(p))
    ss : List<&2, String> <- disk.all(K.pkg.root(p), fs)
    _rm : String <- R.exec(["rm", "-rf", work])
    return W.Got{W.Clone{nar}, K.manifest_of(fs), ss}

# the entry has to be in the checkout for there to be a package to walk
def clone.entry(ok: Bool, +work: String, +entry: String, +url: String, +rev: String, +nar: String) -> IO(W.Answer):
  match ok:
    case True{}:
      clone.walk(work, entry, nar)
    case False{}:
      clone.miss(work, "ez: " ++ entry ++ " is not in " ++ url ++ " at " ++ rev)

# the checkout, weighed and walked
def clone.weigh(+work: String, +url: String, +rev: String, +entry: String) -> IO(W.Answer):
  do IO<W.Answer>:
    _dg : String <- R.exec(["rm", "-rf", work ++ "/.git"])
    +s : Say.Spin <- Say.hold(Say.hashing(rev))
    +nar : String <- Git.nar(work)
    Say.done(s)
    +ck : String <- R.exec(["test", "-f", P.join(work, entry)])
    clone.entry(R.ok(ck), work, entry, url, rev, nar)

# a git package whose tree is not under BEND_LIB: a shallow clone at the rev
# the ledger pins, the way `ez add` and `ez fetch` clone, with a relative path
# source resolved against the project root (`Git.anchored`). Nothing is laid
# here; the plan lays the tree once it has checked it.
def answer.clone(+lib: String, +hash: String, +url: String, +rev: String, +entry: String) -> IO(W.Answer):
  +work = lib ++ "/.work-" ++ hash
  do IO<W.Answer>:
    _rm : String <- R.exec(["rm", "-rf", work])
    _mk : String <- R.exec(["mkdir", "-p", work])
    +s : Say.Spin <- Say.hold(Say.dep.git(Say.label(hash, entry), url))
    +from : String <- Git.anchored(url)
    a : W.Answer <- clone.run(work, "init", ["git", "init", "-q", work], _u =>
      clone.run(work, "fetch", ["git", "-C", work, "fetch", "-q", "--depth", "1", from, rev], _v =>
        clone.run(work, "checkout", ["git", "-C", work, "checkout", "-q", rev], _w =>
          clone.weigh(work, url, rev, entry))))
    Say.done(s)
    return a

# a tree already under BEND_LIB is read; a missing one is cloned
def git.seen(
  got: Maybe<&2, String>,
  +lib: String,
  +hash: String,
  +url: String,
  +rev: String,
  +entry: String
) -> IO(W.Answer):
  match got:
    case Some{text}:
      answer.lib(lib ++ "/" ++ hash, text)
    case None{}:
      answer.clone(lib, hash, url, rev, entry)

# a git package
def answer.git(+lib: String, +hash: String, +url: String, +rev: String, +entry: String) -> IO(W.Answer):
  do IO<W.Answer>:
    m : Maybe<&2, String> <- F.read(lib ++ "/" ++ hash ++ "/manifest")
    git.seen(m, lib, hash, url, rev, entry)

# one question, answered
def answer(+lib: String, ask: W.Ask) -> IO(W.Answer):
  W.Pkg{+hash, src, +hub} = ask
  match src:
    case L.Hub{}:
      answer.hub(hub, hash)
    case L.Git{url, rev, entry, _root, _nar, _tag}:
      answer.git(lib, hash, url, rev, entry)

# every question, answered
def answer.all(+lib: String, asks: List<&2, W.Ask>) -> IO(List<&2, W.Reply>):
  match asks:
    case []:
      IO.pure(List<&2, W.Reply>, [])
    case +h <> t:
      do IO<List<&2, W.Reply>>:
        a : W.Answer <- answer(lib, h)
        rest : List<&2, W.Reply> <- answer.all(lib, t)
        return W.Reply{h, a} <> rest

# ---------------------------------------------------------------------------
# answering the upgrade's questions

# what git printed, and whether it succeeded, kept as it was
def git.said(+what: String, args: List<&2, String>) -> IO(Up.Answer):
  do IO<Up.Answer>:
    +s : Say.Spin <- Say.hold(what)
    +out : String <- R.exec(args)
    Say.done(s)
    return Up.Printed{R.ok(out), R.text(out)}

# the refs a ref could name: a tag, its peeled form, and a branch, all at
# once, because which of them exists is the question
def answer.refs(+url: String, +ref: String) -> IO(Up.Answer):
  do IO<Up.Answer>:
    +from : String <- Git.anchored(url)
    git.said(Say.resolving.at(url), ["git", "ls-remote", from, "refs/tags/" ++ ref,
      "refs/tags/" ++ ref ++ "^{}", "refs/heads/" ++ ref])

# HEAD on the remote, with the branch it is a symref to
def answer.head(+url: String) -> IO(Up.Answer):
  do IO<Up.Answer>:
    +from : String <- Git.anchored(url)
    git.said(Say.resolving.at(url), ["git", "ls-remote", "--symref", from, "HEAD"])

# every tag on the remote
def answer.tags(+url: String) -> IO(Up.Answer):
  do IO<Up.Answer>:
    +from : String <- Git.anchored(url)
    git.said(Say.resolving.at(url), ["git", "ls-remote", "--tags", from])

# whether `tip` descends from `pin`, asked of a blobless bare clone
def answer.above(+lib: String, +url: String, +pin: String, +tip: String) -> IO(Up.Answer):
  do IO<Up.Answer>:
    yes : Bool <- Git.descendant.at(lib ++ "/.work-above", url, pin, tip)
    return Up.Onward{yes}

# the checkout's package, walked from its entry the way `ez add` walks it, with
# the directory its paths are written from, against the repo
def tree.walk(+work: String, +at: String, +nar: String) -> IO(Up.Answer):
  do IO<Up.Answer>:
    +p : K.Pkg <- K.pkg_of(P.join(work, at))
    +fs : List<&2, K.File> <- IO.pure(List<&2, K.File>, K.pkg.files(p))
    ss : List<&2, String> <- disk.all(K.pkg.root(p), fs)
    +rt : String <- IO.pure(String, Git.root.rel(P.join(work, at), K.pkg.root(p), at))
    _rm : String <- R.exec(["rm", "-rf", work])
    return Up.Checkout{nar, rt, K.manifest_of(fs), ss}

# the entry has to be in the checkout for there to be a package to walk
def tree.entry(ok: Bool, +work: String, +at: String, +url: String, +rev: String, +nar: String) -> IO(Up.Answer):
  match ok:
    case True{}:
      tree.walk(work, at, nar)
    case False{}:
      do IO<Up.Answer>:
        _rm : String <- R.exec(["rm", "-rf", work])
        return Up.Miss{"ez: " ++ at ++ " is not in " ++ url ++ " at " ++ rev}

# a checkout at a rev: cloned, its `.git` removed, weighed, and walked. An
# entry that was not recorded is read from the checkout. Nothing is laid and
# nothing is noted: a tree the upgrade moves to is laid by the plan, once the
# upgrade and the lock both succeed.
def answer.tree(+lib: String, +url: String, +rev: String, +entry: String) -> IO(Up.Answer):
  +work = lib ++ "/.work-" ++ rev
  do IO<Up.Answer>:
    _rm : String <- R.exec(["rm", "-rf", work])
    _mk : String <- R.exec(["mkdir", "-p", work])
    Git.clone(work, url, rev)
    +at : String <- Git.entry.for(Bool.not(String.is_empty(entry)), entry, work)
    _dg : String <- R.exec(["rm", "-rf", work ++ "/.git"])
    +s : Say.Spin <- Say.hold(Say.hashing(rev))
    +nar : String <- Git.nar(work)
    Say.done(s)
    +ck : String <- R.exec(["test", "-f", P.join(work, at)])
    tree.entry(R.ok(ck), work, at, url, rev, nar)

# a commit's NAR hash, for a tool
def answer.weigh(+url: String, +rev: String) -> IO(Up.Answer):
  do IO<Up.Answer>:
    +nar : String <- Git.weigh(url, rev)
    return Up.Weighed{nar}

# the hub's manifest for a hash a dependency moved to
def answer.hubhas(+hub: String, +hash: String) -> IO(Up.Answer):
  do IO<Up.Answer>:
    g : Web.Got <- Web.fetch(L.url_of(hub, hash, "manifest"), L.want(hash))
    return Up.HubSaid{g}

# the ignore file, "" when it is missing
def answer.ignore() -> IO(Up.Answer):
  do IO<Up.Answer>:
    m : Maybe<&2, String> <- F.read(".gitignore")
    return Up.Text{F.text_of(m)}

# one source in front of the rest, or the first that could not be read
def found.put(got: Maybe<&2, String>, +at: String, rest: Up.Answer) -> Up.Answer:
  match got:
    case None{}:
      Up.Miss{"ez: " ++ at ++ " could not be read"}
    case Some{text}:
      match rest:
        case Up.Files{fs}:
          Up.Files{Up.Found{at, text} <> fs}
        case _:
          rest

# every listed source, read
def found.all(ps: List<&2, String>) -> IO(Up.Answer):
  match ps:
    case []:
      IO.pure(Up.Answer, Up.Files{[]})
    case +h <> t:
      do IO<Up.Answer>:
        m : Maybe<&2, String> <- F.read(h)
        rest : Up.Answer <- found.all(t)
        return found.put(m, h, rest)

def found.listed(ok: Bool, +text: String) -> IO(Up.Answer):
  match ok:
    case True{}:
      found.all(nonempty(String.lines(text)))
    case False{}:
      IO.pure(Up.Answer, Up.Miss{"ez: could not list sources: " ++ String.trim(text)})

# every Bend source of the project. Vendored trees and the gate's shadow live
# under .ez, and a checkout's .git is not source, so neither is rewritten.
def answer.sources() -> IO(Up.Answer):
  do IO<Up.Answer>:
    +out : String <- R.exec(["find", ".", "-name", "*.bend",
      "-not", "-path", "*/.ez/*", "-not", "-path", "*/.git/*"])
    found.listed(R.ok(out), R.text(out))

# one of the upgrade's questions, answered
def answer.up(+lib: String, ask: Up.Ask) -> IO(Up.Answer):
  match ask:
    case Up.Refs{url, ref}:
      answer.refs(url, ref)
    case Up.Head{url}:
      answer.head(url)
    case Up.Tags{url}:
      answer.tags(url)
    case Up.Above{url, pin, tip}:
      answer.above(lib, url, pin, tip)
    case Up.Tree{url, rev, entry}:
      answer.tree(lib, url, rev, entry)
    case Up.Weigh{url, rev}:
      answer.weigh(url, rev)
    case Up.HubHas{hub, hash}:
      answer.hubhas(hub, hash)
    case Up.Ignore{}:
      answer.ignore()
    case Up.Sources{}:
      answer.sources()

# every one of them, answered
def answer.ups(+lib: String, asks: List<&2, Up.Ask>) -> IO(List<&2, Up.Reply>):
  match asks:
    case []:
      IO.pure(List<&2, Up.Reply>, [])
    case +h <> t:
      do IO<List<&2, Up.Reply>>:
        a : Up.Answer <- answer.up(lib, h)
        rest : List<&2, Up.Reply> <- answer.ups(lib, t)
        return Up.Reply{h, a} <> rest

# the World with more answers in it
def more(world: W.World, rs: List<&2, W.Reply>, us: List<&2, Up.Reply>) -> W.World:
  W.World{args, ledger, listing, replies, ups} = world
  W.World{args, ledger, listing, List.append(&2, W.Reply, replies, rs),
    List.append(&2, Up.Reply, ups, us)}

# ---------------------------------------------------------------------------
# executing a plan

# a write that did not happen stops the command
def wrote(ok: Bool, +at: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, "ez: " ++ at ++ " could not be written")

# one file written, with the directory it goes in made first
def write(+at: String, text: String) -> IO(Unit):
  do IO<Unit>:
    _mk : String <- R.exec(["mkdir", "-p", P.dir(at)])
    ok : Bool <- F.write(at, text)
    wrote(ok, at)

# every file of a tree, in order
def lay.all(+dir: String, fs: List<&2, W.Source>) -> IO(Unit):
  match fs:
    case []:
      IO.pure(Unit, Unit{})
    case W.Source{at, text} <> t:
      do IO<Unit>:
        write(dir ++ "/" ++ at, text)
        lay.all(dir, t)

# where a place is
def place(+lib: String, pl: Plan.Place) -> String:
  match pl:
    case Plan.Committed{}:
      ".ez/lib"
    case Plan.Cache{}:
      lib

# one effect
def exec(+lib: String, effect: Plan.Effect) -> IO(Unit):
  match effect:
    case Plan.Write{at, text}:
      write(at, text)
    case Plan.Lay{pl, hash, fs}:
      +dir = place(lib, pl) ++ "/" ++ hash
      do IO<Unit>:
        _rm : String <- R.exec(["rm", "-rf", dir])
        lay.all(dir, fs)
    case Plan.Drop{hash}:
      do IO<Unit>:
        _rm : String <- R.exec(["rm", "-rf", ".ez/lib/" ++ hash])
        return Unit{}
    case Plan.Say{text}:
      IO.print(text)

# every effect, in order
def exec.all(+lib: String, es: List<&2, Plan.Effect>) -> IO(Unit):
  match es:
    case []:
      IO.pure(Unit, Unit{})
    case h <> t:
      do IO<Unit>:
        exec(lib, h)
        exec.all(lib, t)

# how the command ends
def end(outcome: Plan.Outcome) -> IO(Unit):
  match outcome:
    case Plan.Success{}:
      IO.pure(Unit, Unit{})
    case Plan.Refused{why}:
      IO.die(Unit, 1, why)

# a plan, executed
def exec.plan(+lib: String, pl: Plan.Plan) -> IO(Unit):
  Plan.Plan{es, outcome} = pl
  do IO<Unit>:
    exec.all(lib, es)
    end(outcome)

# ---------------------------------------------------------------------------
# the loop

# the planner's step: its questions answered and the loop gone round again,
# or its plan run
def loop.step(st: Plan.Step, +lib: String, world: W.World, go: W.World -> IO(Unit)) -> IO(Unit):
  match st:
    case Plan.Asking{asks, ups}:
      do IO<Unit>:
        rs : List<&2, W.Reply> <- answer.all(lib, asks)
        us : List<&2, Up.Reply> <- answer.ups(lib, ups)
        go(more(world, rs, us))
    case Plan.Run{pl}:
      exec.plan(lib, pl)

# the loop, under fuel. Every round adds at least one answer, since the
# planner never asks what the World answers already.
def loop(fuel: Nat, +lib: String, +world: W.World) -> IO(Unit):
  match fuel:
    case 0n:
      IO.die(Unit, 1, "ez: the lock kept asking questions")
    case 1n+f:
      loop.step(Plan.step(world), lib, world, w => loop(f, lib, w))

# `ez lock`: the ledger and the listing read, every question answered, and
# the plan run
def run(args: W.Args) -> IO(Unit):
  do IO<Unit>:
    IO.print_err(Say.resolving())
    lib : String <- bend.lib()
    led : Maybe<&2, String> <- read.ledger()
    ls : W.Listing <- read.listing()
    loop(U32.to_nat(100000), lib, W.World{args, led, ls, [], []})

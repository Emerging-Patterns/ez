# tool/plan: `ez tool run`, `install` and `upgrade` as a pure planner, and
# `ez tool sync` as the list of installs it runs. The planner reads a World
# (tool/world.bend) and returns either the questions it still needs answered
# (`step`) or a Plan. The interpreter (tool/run.bend) loops on `step`,
# answering each question by IO, then executes the plan.
#
# Before it asks anything the planner refuses what needs no answer: an
# install or upgrade with nowhere to link (EZ-TOOL-1), no cache root, a
# project ledger that does not parse, a target that names nothing or a cache
# slug that could leave the cache (EZ-TOOL-8), a name the ledger pins that
# the lock does not, or pins at no commit. Then it resolves the commit
# (EZ-TOOL-4): a `[tools.*]` pin is the lock's rev, url, entry and bin; a
# remote is what its HEAD names; a path is its clean HEAD, and a path with
# uncommitted or untracked changes, or one that is not the top of a
# checkout, is no commit (EZ-TOOL-3). Then the checkout: a remote's is
# cached per commit and read from there when its record says it finished,
# otherwise asked of git with every file's text; a path is read where it is.
# Then its ledger, which names the file built (EZ-TOOL-7) and the link, and
# a name that is not a TOML bare key is refused. A checkout with no ez.toml
# is a plain Bend repository: it builds `main.bend`, or the file `--entry`
# names, needs no lock, and is linked under that file's stem, or under the
# repository's name when the stem is `main`. A file to build that is not in
# the checkout is refused. Then the binary's record:
# the binary is reused only when it is there and its record is this commit,
# this file and this bend (EZ-TOOL-2). Every binary lives in a directory
# named by its record, so no two records share one, and a link made by an
# install is never rebuilt under it by a run of another commit or file.
#
# The plan of a command that goes on, in order: the checkout laid under the
# cache when it was cloned, with its record written last; the lock fetched,
# for an ez project, and the binary built with its record, unless it is
# reused; then the
# program started, for `run`, or the link written, for `install` and
# `upgrade`. A refusal has no effect at all. The program is started only as
# the last thing, so its status is the command's (EZ-TOOL-5), and `install`
# and `upgrade` never start it (EZ-TOOL-6).
import Base
import ./world.bend as TW
import ../lock/plan.bend as P
import ../lock/up.bend as Up
import ../ledger/manifest.bend as M
import ../toml/toml.bend as T
import ../pkg/pkg.bend as K
import ../pkg/path.bend as Path
import ../git/git.bend as Git
import ../ez/target.bend as Tgt
import ../ez/named.bend as Named
import ../ez/key.bend as Key
import ../ez/say.bend as Say
import ../sha/sha.bend as Sha

# ---------------------------------------------------------------------------
# small pieces

# whether a Maybe holds nothing
def none(got: Maybe<&2, String>) -> Bool:
  match got:
    case None{}:
      True{}
    case Some{_t}:
      False{}

# whether an act links the binary: `install` and `upgrade` do, `run` does not
def links.act(act: TW.Act) -> Bool:
  match act:
    case TW.Run{_args}:
      False{}
    case TW.Install{}:
      True{}
    case TW.Upgrade{}:
      True{}

# the tools of a ledger that was read
def tools.of(manifest: M.Manifest) -> List<&2, M.Tool>:
  M.Manifest{_n, _e, _b, _h, _pa, _pv, _ds, ts} = manifest
  ts

# the pins a lock's text records
def locked(+body: String) -> List<&2, M.Tool>:
  M.tools(T.sects(T.parse(body)))

# ---------------------------------------------------------------------------
# what the target names

# a target resolved as far as the project can say: a `[tools.*]` pin, with
# the lock's url and rev and the file its `bin` or `entry` names; a free
# target, with the place its word names; or why there is none
type Src is Data:
  Pin{name: String, url: String, rev: String, over: String}
  Free{place: Tgt.Place}
  NoSrc{why: String}

# the file a pin names: its `bin`, else its `entry`, else "" so the
# checkout's own ledger chooses
def over.of(+binary: String, +entry: String) -> String:
  Bool.pick(String, String.is_empty(binary), entry, binary)

# a pin the lock has, or a refusal when it has none by that name
def pin.go(empty: Bool, +tool: M.Tool, +name: String) -> Src:
  match empty:
    case True{}:
      NoSrc{"ez: " ++ name ++ " is not pinned in ez.lock.toml"}
    case False{}:
      Pin{name, M.source.url(M.tool.source(tool)), M.source.rev(M.tool.source(tool)),
        over.of(M.tool.bin(tool), M.tool.entry(tool))}

# the pin the lock has for a name, or a refusal
def pin.of(+tool: M.Tool, +name: String) -> Src:
  pin.go(String.is_empty(M.tool.name(tool)), tool, name)

# the pin the lock records under a name, one with empty fields for none
def pin.in(+body: String, +name: String) -> M.Tool:
  M.tool.find(locked(body), name)

# a name the ledger pins is built as the lock pins it
def pinned(got: Maybe<&2, String>, +name: String) -> Src:
  match got:
    case None{}:
      NoSrc{"ez: ez.lock.toml is not there"}
    case Some{body}:
      pin.of(pin.in(body, name), name)

# a name the ledger pins, or a free target
def src.pick(free: Bool, +world: TW.World) -> Src:
  match free:
    case True{}:
      Free{Tgt.classify(TW.target(world))}
    case False{}:
      pinned(TW.lock(world), TW.target(world))

# whether a ledger pins nothing under this name
def unpinned(+manifest: M.Manifest, +name: String) -> Bool:
  String.is_empty(M.tool.name(M.tool.find(tools.of(manifest), name)))

# a project ledger that does not parse is refused
def src.read(led: M.Read, +world: TW.World) -> Src:
  match led:
    case M.Bad{why}:
      NoSrc{"ez: error: " ++ why}
    case M.Good{m}:
      src.pick(unpinned(m, TW.target(world)), world)

# what the target names (EZ-TOOL-4)
def src(+world: TW.World) -> Src:
  src.read(TW.project(world), world)

# a pin names a git repository; a path is no pin
def place.pin(pl: Tgt.Place) -> Tgt.Place:
  match pl:
    case Tgt.Bad{why}:
      Tgt.Bad{why}
    case Tgt.Local{_p}:
      Tgt.Bad{"a pinned tool names a git repo"}
    case Tgt.Remote{url, slug}:
      Tgt.Remote{url, slug}

# where a resolved target is
def place.of(found: Src) -> Tgt.Place:
  match found:
    case Pin{_n, url, _r, _o}:
      place.pin(Tgt.classify(url))
    case Free{pl}:
      pl
    case NoSrc{why}:
      Tgt.Bad{why}

# where the target is: a remote with its cache slug, a path, or nowhere
def place(+world: TW.World) -> Tgt.Place:
  place.of(src(world))

# the file a pin names, "" for a free target
def over.src(found: Src) -> String:
  match found:
    case Pin{_n, _u, _r, o}:
      o
    case Free{_pl}:
      ""
    case NoSrc{_why}:
      ""

# the file the target names for itself, "" when the checkout chooses
def over(+world: TW.World) -> String:
  over.src(src(world))

# ---------------------------------------------------------------------------
# the commit

# what git said of a local path, still to ask, or why there is nothing
type Loc is Data:
  Loc{abs: String, top: String, head: String, ok: Bool, status: String}
  LocWait{ask: TW.Ask}
  LocNo{why: String}

# what git said of a path, looked up
def loc.of(got: TW.Heard, ask: TW.Ask) -> Loc:
  match got:
    case TW.Open{}:
      LocWait{ask}
    case TW.Heard{answer}:
      match answer:
        case TW.Located{abs, top, head, ok, status}:
          Loc{abs, top, head, ok, status}
        case TW.Miss{why}:
          LocNo{why}
        case _:
          LocNo{"ez: a path was not answered with what git says of it"}

# the question about a local path, `~` expanded
def locate(+path: String, +world: TW.World) -> TW.Ask:
  TW.Locate{Tgt.expand(TW.home(world), path)}

# what git said of a local path
def loc(+path: String, +world: TW.World) -> Loc:
  loc.of(TW.heard(world, locate(path, world)), locate(path, world))

# the real path of a local target, "" while it is not known
def loc.abs(spot: Loc) -> String:
  match spot:
    case Loc{abs, _t, _h, _ok, _s}:
      abs
    case LocWait{_a}:
      ""
    case LocNo{_why}:
      ""

# the commit a local path builds: HEAD, when `git status` answered and named
# nothing, and the path is the top of its checkout. A path in a checkout
# whose top is elsewhere may be ignored there, or hold files the commit does
# not; either way it is no commit (EZ-TOOL-3).
def local.same(same: Bool, +head: String) -> String:
  match same:
    case True{}:
      head
    case False{}:
      ""

def local.clean(clean: Bool, same: Bool, +head: String) -> String:
  match clean:
    case True{}:
      local.same(same, head)
    case False{}:
      ""

def local.go(ok: Bool, clean: Bool, same: Bool, +head: String) -> String:
  match ok:
    case True{}:
      local.clean(clean, same, head)
    case False{}:
      ""

def local.rev(+abs: String, +top: String, +head: String, ok: Bool, +status: String) -> String:
  local.go(ok, String.is_empty(status), String.eq(top, abs), head)

# the commit of a local target, "" while it is not known
def loc.rev(spot: Loc) -> String:
  match spot:
    case Loc{abs, top, head, ok, status}:
      local.rev(abs, top, head, ok, status)
    case LocWait{_a}:
      ""
    case LocNo{_why}:
      ""

# what a remote's HEAD printed
def head.said(+world: TW.World, +url: String) -> Up.Said:
  Up.printed(TW.ups(world), Up.Head{url}, "ls-remote " ++ url)

# the commit HEAD names, "" while it is not known
def head.rev(said: Up.Said) -> String:
  match said:
    case Up.Said{text}:
      Git.tip.rev(Git.rows(String.lines(text)))
    case Up.Unsaid{_why}:
      ""
    case Up.Unasked{_ask}:
      ""

# the commit of a free target
def rev.free(pl: Tgt.Place, +world: TW.World) -> String:
  match pl:
    case Tgt.Bad{_why}:
      ""
    case Tgt.Local{p}:
      loc.rev(loc(p, world))
    case Tgt.Remote{url, _slug}:
      head.rev(head.said(world, url))

# the commit of a resolved target
def rev.of(found: Src, +world: TW.World) -> String:
  match found:
    case Pin{_n, _u, r, _o}:
      r
    case Free{pl}:
      rev.free(pl, world)
    case NoSrc{_why}:
      ""

# the commit built, "" for none (EZ-TOOL-4)
def rev(+world: TW.World) -> String:
  rev.of(src(world), world)

# ---------------------------------------------------------------------------
# where things are

# the cache root, "" for none
def root(+world: TW.World) -> String:
  TW.text.or(TW.cache.of(world))

# the cache directory of a target: `<root>/<slug>` for a remote, and
# `<root>/local<abs>` for a path
def dir.of(pl: Tgt.Place, +root: String, +world: TW.World) -> String:
  match pl:
    case Tgt.Bad{_why}:
      root
    case Tgt.Local{p}:
      root ++ "/local" ++ loc.abs(loc(p, world))
    case Tgt.Remote{_url, slug}:
      root ++ "/" ++ slug

# the target's cache directory
def dir(+world: TW.World) -> String:
  dir.of(place(world), root(world), world)

# a remote's checkout of a commit lives in its own directory, so a pin and a
# free run at other commits never clone over each other
def revdir(+world: TW.World) -> String:
  dir(world) ++ "/" ++ rev(world)

# the checkout's record, written once every file of it is laid
def stamp.at(+world: TW.World) -> String:
  revdir(world) ++ "/rev"

# the checkout: under the cache for a remote, the path itself for a path
def top.of(pl: Tgt.Place, +world: TW.World) -> String:
  match pl:
    case Tgt.Bad{_why}:
      ""
    case Tgt.Local{p}:
      loc.abs(loc(p, world))
    case Tgt.Remote{_url, _slug}:
      revdir(world) ++ "/src"

# where the checkout is
def top(+world: TW.World) -> String:
  top.of(place(world), world)

# the library the checkout's lock is fetched into: the checkout's own for a
# remote, and one under the cache for a path, which is never written into
def lib.of(pl: Tgt.Place, +world: TW.World) -> String:
  match pl:
    case Tgt.Bad{_why}:
      ""
    case Tgt.Local{_p}:
      dir(world) ++ "/lib"
    case Tgt.Remote{_url, _slug}:
      top(world) ++ "/.ez/lib"

# ---------------------------------------------------------------------------
# answers read

# a file's text as it was answered, None when it is missing or not answered
def text.of(got: TW.Heard) -> Maybe<&2, String>:
  match got:
    case TW.Open{}:
      None{}
    case TW.Heard{answer}:
      match answer:
        case TW.Text{m}:
          m
        case _:
          None{}

def read.got(+world: TW.World, +path: String) -> Maybe<&2, String>:
  text.of(TW.heard(world, TW.Read{path}))

# whether a question is still open
def open.of(got: TW.Heard) -> Bool:
  match got:
    case TW.Open{}:
      True{}
    case TW.Heard{_a}:
      False{}

# whether a question of ours is still open
def open(+world: TW.World, +ask: TW.Ask) -> Bool:
  open.of(TW.heard(world, ask))

# a question kept when it is still open
def opens.step(open: Bool, ask: TW.Ask, rest: List<&2, TW.Ask>) -> List<&2, TW.Ask>:
  match open:
    case True{}:
      ask <> rest
    case False{}:
      rest

# the questions of these still open
def opens(+world: TW.World, asks: List<&2, TW.Ask>) -> List<&2, TW.Ask>:
  match asks:
    case []:
      []
    case +h <> t:
      opens.step(open(world, h), h, opens(world, t))

# whether an answer said yes
def yes.of(got: TW.Heard) -> Bool:
  match got:
    case TW.Open{}:
      False{}
    case TW.Heard{answer}:
      match answer:
        case TW.Is{yes}:
          yes
        case _:
          False{}

# ---------------------------------------------------------------------------
# the checkout

# the checkout's ledger and lock, read where it is; the files of one cloned
# now; the questions still open; or why there is none
type Co is Data:
  Kept{toml: Maybe<&2, String>, lock: Maybe<&2, String>}
  Laid{files: List<&2, K.Source>}
  CoWait{asks: List<&2, TW.Ask>, ups: List<&2, Up.Ask>}
  CoNo{why: String}

# the files a checkout at a rev is made of, asked of git
def clone.ask(+world: TW.World, +url: String) -> Up.Ask:
  Up.Clone{url, rev(world)}

# the checkout git gave, still to ask, or why there is none
def co.clone(got: Up.Heard, ask: Up.Ask) -> Co:
  match got:
    case Up.Open{}:
      CoWait{[], [ask]}
    case Up.Heard{answer}:
      match answer:
        case Up.Cloned{_nar, fs}:
          Laid{fs}
        case Up.Miss{why}:
          CoNo{why}
        case _:
          CoNo{"ez: a checkout was not answered with one"}

# the three files of a cached checkout
def reads(+world: TW.World) -> List<&2, TW.Ask>:
  [TW.Read{stamp.at(world)}, TW.Read{top(world) ++ "/ez.toml"},
    TW.Read{top(world) ++ "/ez.lock.toml"}]

# the cached checkout is this commit and finished, or it is cloned again
def co.fresh(fresh: Bool, +url: String, +world: TW.World) -> Co:
  match fresh:
    case True{}:
      Kept{read.got(world, top(world) ++ "/ez.toml"), read.got(world, top(world) ++ "/ez.lock.toml")}
    case False{}:
      co.clone(Up.heard(TW.ups(world), clone.ask(world, url)), clone.ask(world, url))

# whether the cached checkout's record names this commit. The record is
# written after every file, so a checkout it names is whole, with or without
# a ledger.
def fresh(+world: TW.World) -> Bool:
  Key.checkout(String.trim(TW.text.or(read.got(world, stamp.at(world)))), rev(world))

# a remote's cached checkout, once its three files are read
def co.remote(open: List<&2, TW.Ask>, +url: String, +world: TW.World) -> Co:
  match open:
    case []:
      co.fresh(fresh(world), url, world)
    case h <> t:
      CoWait{h <> t, []}

# a path's ledger and lock, once they are read
def co.local(open: List<&2, TW.Ask>, +world: TW.World) -> Co:
  match open:
    case []:
      Kept{read.got(world, top(world) ++ "/ez.toml"), read.got(world, top(world) ++ "/ez.lock.toml")}
    case h <> t:
      CoWait{h <> t, []}

# the checkout of a place
def co.of(pl: Tgt.Place, +world: TW.World) -> Co:
  match pl:
    case Tgt.Bad{why}:
      CoNo{"ez: " ++ why}
    case Tgt.Local{_p}:
      co.local(opens(world, [TW.Read{top(world) ++ "/ez.toml"},
        TW.Read{top(world) ++ "/ez.lock.toml"}]), world)
    case Tgt.Remote{url, _slug}:
      co.remote(opens(world, reads(world)), url, world)

# the checkout of the target
def co(+world: TW.World) -> Co:
  co.of(place(world), world)

# the checkout's ez.toml
def co.toml(checkout: Co) -> Maybe<&2, String>:
  match checkout:
    case Kept{t, _l}:
      t
    case Laid{fs}:
      K.look(fs, "ez.toml")
    case CoWait{_as, _us}:
      None{}
    case CoNo{_why}:
      None{}

# the checkout's ez.lock.toml
def co.lock(checkout: Co) -> Maybe<&2, String>:
  match checkout:
    case Kept{_t, l}:
      l
    case Laid{fs}:
      K.look(fs, "ez.lock.toml")
    case CoWait{_as, _us}:
      None{}
    case CoNo{_why}:
      None{}

# ---------------------------------------------------------------------------
# the checkout's ledger, and the binary

# the checkout, as a person knows it: a remote at its commit, or a path
def label.of(pl: Tgt.Place, +world: TW.World) -> String:
  match pl:
    case Tgt.Bad{why}:
      why
    case Tgt.Local{_p}:
      top(world)
    case Tgt.Remote{url, _slug}:
      url ++ " at " ++ rev(world)

# the checkout, as a person knows it
def label(+world: TW.World) -> String:
  label.of(place(world), world)

# the checkout's ledger as read. A checkout with no ez.toml is a plain Bend
# repository, whose ledger names nothing: no package, no entry, no deps.
def led.of(got: Maybe<&2, String>) -> M.Read:
  match got:
    case None{}:
      M.Good{M.Manifest{"", "", "", "", "", "", [], []}}
    case Some{text}:
      M.parse(text)

# the checkout's ledger, read
def led(+world: TW.World) -> M.Read:
  led.of(co.toml(co(world)))

# whether the checkout is a plain Bend repository: it has no ez.toml, so no
# git dependencies and no lock. Its program's hub imports are bend's to
# fetch, into a library of its own under the cache.
def plain(+world: TW.World) -> Bool:
  none(co.toml(co(world)))

# where the checkout's lock is fetched, or, for a plain repository, where
# bend fetches its hub imports: a library of the target's own under the
# cache, beside its binaries
def lib(+world: TW.World) -> String:
  Bool.pick(String, plain(world), dir(world) ++ "/lib", lib.of(place(world), world))

# the model of a ledger that read, an empty one otherwise
def man.of(parsed: M.Read) -> M.Manifest:
  match parsed:
    case M.Bad{_why}:
      M.Manifest{"", "", "", "", "", "", [], []}
    case M.Good{m}:
      m

# the checkout's ledger, empty when it did not read
def man(+world: TW.World) -> M.Manifest:
  man.of(led(world))

# the checkout's `[package] name`, `bin` and `entry`
def man.name(manifest: M.Manifest) -> String:
  M.Manifest{n, _e, _b, _h, _pa, _pv, _ds, _ts} = manifest
  n

# a ledger's `bin`
def man.bin(manifest: M.Manifest) -> String:
  M.Manifest{_n, _e, b, _h, _pa, _pv, _ds, _ts} = manifest
  b

# a ledger's `entry`
def man.entry(manifest: M.Manifest) -> String:
  M.Manifest{_n, e, _b, _h, _pa, _pv, _ds, _ts} = manifest
  e

# a file's last component without its `.bend`: `src/cli.bend` is `cli`
def stem(+file: String) -> String:
  Path.unbend(Path.base(file))

# a repository's name: the last component of its URL or path, a trailing
# slash and `.git` taken off, so `https://github.com/o/bolt.git` is `bolt`
def repo.name(+url: String) -> String:
  Path.base(Tgt.ungit(Tgt.unslash(url)))

# the link's name for a plain repository: the stem of the file built, or the
# repository's name when that is `main`, since every plain repository has one
def plain.name(+file: String, +url: String) -> String:
  Bool.pick(String, String.eq(stem(file), "main"), repo.name(url), stem(file))

# where the checkout came from, as a person named it: a remote's URL, or a
# path's real path
def origin.of(pl: Tgt.Place, +world: TW.World) -> String:
  match pl:
    case Tgt.Bad{_why}:
      ""
    case Tgt.Local{_p}:
      top(world)
    case Tgt.Remote{url, _slug}:
      url

# where the checkout came from
def origin(+world: TW.World) -> String:
  origin.of(place(world), world)

# the checkout's `bin`
def bin(+world: TW.World) -> String:
  man.bin(man(world))

# the checkout's `entry`
def entry(+world: TW.World) -> String:
  man.entry(man(world))

# whether a package name can name the link and the binary: none at all, or a
# TOML bare key, so it holds no `/` and cannot be `..`
def name.ok(+name: String) -> Bool:
  Bool.or(String.is_empty(name), Named.bare(name))

# the file built: the pin's `bin`, then its `entry`, then the checkout's
# `bin`, then its `entry`, then `main.bend` (EZ-TOOL-7)
def chosen(+over: String, +binary: String, +entry: String) -> String:
  Bool.pick(String, String.is_empty(over), Tgt.file.of(binary, entry), over)

# the file asked for ahead of the checkout's own: the pin's `bin` or
# `entry`, else the file `--entry` names, else "" so the checkout chooses. A
# pin is what the project decided, so a flag does not move it; over a
# checkout's ledger the flag wins, as cargo's `--bin` does.
def wish(+over: String, +want: String) -> String:
  Bool.pick(String, String.is_empty(over), want, over)

# the file built, relative to the checkout: `main.bend` for a plain
# repository unless `--entry` names another (EZ-TOOL-7)
def choice(+world: TW.World) -> String:
  chosen(wish(over(world), TW.want(world)), bin(world), entry(world))

# the file built, in the checkout
def file(+world: TW.World) -> String:
  Path.join(top(world), choice(world))

# a path's part under a directory, "" when it is not under it
def inside(+dir: String, +path: String) -> String:
  Bool.pick(String, String.starts_with(path, dir ++ "/"),
    String.drop(path, Nat.add(String.length(dir), 1n)), "")

# whether the file built is in the checkout: among the files git gave, or
# read where the checkout is. A file outside the checkout is not in it.
def present.of(checkout: Co, +world: TW.World) -> Bool:
  match checkout:
    case Laid{fs}:
      Bool.not(none(K.look(fs, inside(top(world), file(world)))))
    case Kept{_t, _l}:
      Bool.and(Bool.not(String.is_empty(inside(top(world), file(world)))),
        Bool.not(none(read.got(world, file(world)))))
    case CoWait{_as, _us}:
      False{}
    case CoNo{_why}:
      False{}

# whether the file built is there
def present(+world: TW.World) -> Bool:
  present.of(co(world), world)

# the question whether the file built is there, for a checkout read where it
# is; git gave every file of one cloned now
def file.asks.of(checkout: Co, +world: TW.World) -> List<&2, TW.Ask>:
  match checkout:
    case Kept{_t, _l}:
      opens(world, [TW.Read{file(world)}])
    case Laid{_fs}:
      []
    case CoWait{_as, _us}:
      []
    case CoNo{_why}:
      []

def file.asks(+world: TW.World) -> List<&2, TW.Ask>:
  file.asks.of(co(world), world)

# the name the link and the binary are given: for a plain repository the
# one `plain.name` gives it, and the package's for an ez project
def name.of(bare: Bool, +world: TW.World) -> String:
  match bare:
    case True{}:
      plain.name(choice(world), origin(world))
    case False{}:
      man.name(man(world))

# the name the link and the binary are given
def name.raw(+world: TW.World) -> String:
  name.of(plain(world), world)

# the link's name: the package's, or `app` (EZ-TOOL-7)
def name(+world: TW.World) -> String:
  Tgt.out.name(name.raw(world))

# what the binary is made from: the commit, the file and the bend (EZ-TOOL-2)
def key(+world: TW.World) -> Key.Key:
  Key.Key{rev(world), file(world), TW.bend(world)}

# the directory a record's binary lives in, named by the record
def stamp.of(key: Key.Key) -> String:
  String.take(Sha.hex(Key.show(key)), 16n)

# the directory of this record's binary
def bdir(+world: TW.World) -> String:
  dir(world) ++ "/bin/" ++ stamp.of(key(world))

# the binary
def out(+world: TW.World) -> String:
  bdir(world) ++ "/" ++ name(world) ++ ".out"

def key.at(+world: TW.World) -> String:
  bdir(world) ++ "/key"

# the binary's record as it was written, none when there is none
def was(+world: TW.World) -> Key.Key:
  Key.read(String.trim(TW.text.or(read.got(world, key.at(world)))))

# whether the binary is there
def there(+world: TW.World) -> Bool:
  yes.of(TW.heard(world, TW.Exec{out(world)}))

# the binary is reused when it is there and its record is this one
def reuse(+world: TW.World) -> Bool:
  Bool.and(there(world), Key.reuse(was(world), key(world)))

# ---------------------------------------------------------------------------
# the plan

# the checkout laid under the cache, its record last, or nothing laid
type Lay is Data:
  Lay{dir: String, writes: List<&2, P.Effect>}
  Still{}

# the binary: the lock of the checkout at `top` fetched into the library
# when `fetch` says it has one, the file built into `out` with that library
# as BEND_LIB, and the record written at `at`; or the one there reused; or
# nothing, for a command that refuses
type Make is Data:
  Make{top: String, lib: String, fetch: Bool, file: String, out: String, at: String,
    key: String, name: String}
  Reuse{name: String}
  Skip{}

# what is done with the binary: started with these words, as the last thing;
# linked into `dir` under `name`, with the lines a person is told; or nothing
type Finish is Data:
  Launch{bin: String, args: List<&2, String>}
  Link{bin: String, dir: String, name: String, says: List<&2, String>}
  Idle{}

# everything a tool command does, in order, and how it ends
type Plan is Data:
  Plan{lay: Lay, make: Make, finish: Finish, outcome: P.Outcome}

# every file of a checkout written under its top
def writes.of(+top: String, fs: List<&2, K.Source>) -> List<&2, P.Effect>:
  match fs:
    case []:
      []
    case K.Source{at, text} <> t:
      P.Write{top ++ "/" ++ at, text} <> writes.of(top, t)

# the checkout laid, when git gave it now
def lay.of(checkout: Co, +world: TW.World) -> Lay:
  match checkout:
    case Laid{fs}:
      Lay{revdir(world), List.append(&2, P.Effect, writes.of(top(world), fs),
        [P.Write{stamp.at(world), rev(world) ++ "\n"}])}
    case Kept{_t, _l}:
      Still{}
    case CoWait{_as, _us}:
      Still{}
    case CoNo{_why}:
      Still{}

# the checkout laid under the cache, when it was cloned now
def lay(+world: TW.World) -> Lay:
  lay.of(co(world), world)

# the binary reused, or built with its record
def make.of(reused: Bool, +world: TW.World) -> Make:
  match reused:
    case True{}:
      Reuse{name(world)}
    case False{}:
      Make{top(world), lib(world), Bool.not(plain(world)), file(world), out(world),
        key.at(world), Key.show(key(world)), name(world)}

# the binary built, or reused
def make(+world: TW.World) -> Make:
  make.of(reuse(world), world)

# one step of a scan that may stop at the first hit
def seen.step(here: Bool, rest: Unit -> Bool) -> Bool:
  match here:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# a directory with no trailing slash
def bare(+dir: String) -> String:
  Bool.pick(String, String.ends_with(dir, "/"),
    String.take(dir, Nat.sub(String.length(dir), 1n)), dir)

# whether this directory is one of the entries
def seen(+dir: String, ps: List<&2, String>) -> Bool:
  match ps:
    case []:
      False{}
    case +h <> t:
      seen.step(String.eq(bare(h), bare(dir)), _u => seen(dir, t))

# whether a directory is an entry of `PATH`
def on.path(+dir: String, +path: String) -> Bool:
  seen(dir, String.split(path, ':'))

# the link directory, "" for none
def bin.at(+world: TW.World) -> String:
  TW.text.or(TW.bin.of(TW.env(world)))

# what a person is told once the link is written: that the directory is not
# on PATH, when it is not, and what was linked where
def says(install: Bool, +world: TW.World) -> List<&2, String>:
  +called = name(world)
  +at = bin.at(world) ++ "/" ++ called
  +done = Bool.pick(String, install, Say.installed(called, at), Say.linked(called, at))
  Bool.pick(List<&2, String>, on.path(bin.at(world), TW.env.path(TW.env(world))), [done],
    ["warning: " ++ bin.at(world) ++ " is not on PATH", done])

# the program started, or the link written
def finish.of(act: TW.Act, +world: TW.World) -> Finish:
  match act:
    case TW.Run{args}:
      Launch{out(world), args}
    case TW.Install{}:
      Link{out(world), bin.at(world), name(world), says(True{}, world)}
    case TW.Upgrade{}:
      Link{out(world), bin.at(world), name(world), says(False{}, world)}

# what is done with the binary
def finish(+world: TW.World) -> Finish:
  finish.of(TW.act(world), world)

# the plan once every answer is in and nothing refused
def made(+world: TW.World) -> Plan:
  Plan{lay(world), make(world), finish(world), P.Success{}}

# ---------------------------------------------------------------------------
# where a World stands

# every answer is in, a question is still open, or the command refuses
type Verdict is Data:
  Go{}
  Wait{asks: List<&2, TW.Ask>, ups: List<&2, Up.Ask>}
  Stop{why: String}

# a lock is needed only for a binary that is built, and only by an ez
# project: a plain repository has none to have
def decide.lock(missing: Bool, +world: TW.World) -> Verdict:
  match missing:
    case True{}:
      Stop{"ez: " ++ label(world) ++ " has an ez.toml but no ez.lock.toml; its author " ++
        "runs ez lock to write one"}
    case False{}:
      Go{}

# whether the binary is to be built from an ez project with no lock
def unlocked(+world: TW.World) -> Bool:
  Bool.and(Bool.not(reuse(world)),
    Bool.and(Bool.not(plain(world)), none(co.lock(co(world)))))

# the binary's record and whether it is there, asked together
def cache.asks(+world: TW.World) -> List<&2, TW.Ask>:
  opens(world, [TW.Read{key.at(world)}, TW.Exec{out(world)}])

# the binary's record and whether it is there, still to ask
def decide.cache(open: List<&2, TW.Ask>, +world: TW.World) -> Verdict:
  match open:
    case []:
      decide.lock(unlocked(world), world)
    case h <> t:
      Wait{h <> t, []}

# why a missing file is refused: a file a pin names is the project's to fix,
# and any other can be named with `--entry`
def missing.why(+world: TW.World) -> String:
  +why = "ez: " ++ label(world) ++ " has no " ++ choice(world)
  Bool.pick(String, String.is_empty(over(world)),
    why ++ "; name the file to build with --entry <path.bend>", why)

# a file to build that is not in the checkout is refused
def decide.present(ok: Bool, +world: TW.World) -> Verdict:
  match ok:
    case True{}:
      decide.cache(cache.asks(world), world)
    case False{}:
      Stop{missing.why(world)}

# whether the file to build is there, still to ask
def decide.file(open: List<&2, TW.Ask>, +world: TW.World) -> Verdict:
  match open:
    case []:
      decide.present(present(world), world)
    case h <> t:
      Wait{h <> t, []}

# what a name that could not name a file is: a package's, or the one a
# plain repository would be linked as
def name.what(+world: TW.World) -> String:
  Bool.pick(String, plain(world), " would be linked as ", " names its package ")

# a name that could not name a file is refused
def decide.name(ok: Bool, +world: TW.World) -> Verdict:
  match ok:
    case True{}:
      decide.file(file.asks(world), world)
    case False{}:
      Stop{"ez: " ++ label(world) ++ name.what(world) ++ name.raw(world) ++
        ", which is not a TOML bare key"}

# a checkout ledger that does not parse is refused
def decide.led(parsed: M.Read, +world: TW.World) -> Verdict:
  match parsed:
    case M.Bad{why}:
      Stop{"ez: error: " ++ why}
    case M.Good{_m}:
      decide.name(name.ok(name.raw(world)), world)

# the checkout answered, still to ask, or not to be had
def decide.co(checkout: Co, +world: TW.World) -> Verdict:
  match checkout:
    case Kept{_t, _l}:
      decide.led(led(world), world)
    case Laid{_fs}:
      decide.led(led(world), world)
    case CoWait{as, us}:
      Wait{as, us}
    case CoNo{why}:
      Stop{why}

# what git says of a path, still to ask, or not to be had
def decide.loc(spot: Loc, +world: TW.World) -> Verdict:
  match spot:
    case Loc{_a, _t, _h, _ok, _s}:
      decide.co(co(world), world)
    case LocWait{ask}:
      Wait{[ask], []}
    case LocNo{why}:
      Stop{why}

# a remote's HEAD has to name a commit
def decide.tip(ok: Bool, +url: String, +world: TW.World) -> Verdict:
  match ok:
    case True{}:
      decide.co(co(world), world)
    case False{}:
      Stop{"ez: " ++ url ++ " has no HEAD"}

def decide.said(said: Up.Said, +url: String, +world: TW.World) -> Verdict:
  match said:
    case Up.Said{_text}:
      decide.tip(Git.is_rev(rev(world)), url, world)
    case Up.Unsaid{why}:
      Stop{why}
    case Up.Unasked{ask}:
      Wait{[], [ask]}

# a pin's commit is the lock's; a free remote's is asked of its HEAD
def decide.head(found: Src, +url: String, +world: TW.World) -> Verdict:
  match found:
    case Pin{_n, _u, _r, _o}:
      decide.co(co(world), world)
    case Free{_pl}:
      decide.said(head.said(world, url), url, world)
    case NoSrc{why}:
      Stop{why}

# a slug that could leave the cache is refused (EZ-TOOL-8)
def decide.slug(ok: Bool, +url: String, +world: TW.World) -> Verdict:
  match ok:
    case True{}:
      decide.head(src(world), url, world)
    case False{}:
      Stop{"ez: not a repository"}

def decide.place(pl: Tgt.Place, +world: TW.World) -> Verdict:
  match pl:
    case Tgt.Bad{why}:
      Stop{"ez: " ++ why}
    case Tgt.Local{p}:
      decide.loc(loc(p, world), world)
    case Tgt.Remote{url, slug}:
      decide.slug(Tgt.slug.ok(slug), url, world)

# a pin at no commit cannot be built; its rev is a directory name, so it has
# to be one
def decide.pin(ok: Bool, +name: String, +rev: String, +world: TW.World) -> Verdict:
  match ok:
    case True{}:
      decide.place(place(world), world)
    case False{}:
      Stop{"ez: tools." ++ name ++ " in ez.lock.toml has no commit" ++
        Bool.pick(String, String.is_empty(rev), "", ": " ++ rev)}

# what the target names, or why it names nothing
def decide.src(found: Src, +world: TW.World) -> Verdict:
  match found:
    case Pin{+n, _u, +r, _o}:
      decide.pin(Git.is_rev(r), n, r, world)
    case Free{_pl}:
      decide.place(place(world), world)
    case NoSrc{why}:
      Stop{why}

# no cache root is refused
def decide.root(got: Maybe<&2, String>, +world: TW.World) -> Verdict:
  match got:
    case None{}:
      Stop{"ez: HOME is unset, so there is no cache"}
    case Some{_r}:
      decide.src(src(world), world)

# nowhere to link is refused before anything is built
def decide.bin(nowhere: Bool, +world: TW.World) -> Verdict:
  match nowhere:
    case True{}:
      Stop{"ez: HOME is unset, so there is no bin directory"}
    case False{}:
      decide.root(TW.cache.of(world), world)

# where a World stands
def decide(+world: TW.World) -> Verdict:
  decide.bin(Bool.and(links.act(TW.act(world)), none(TW.bin.of(TW.env(world)))), world)

# the plan for where the World stands. One that still asks is a World the
# interpreter did not finish, and is refused rather than guessed at.
def plan.v(verdict: Verdict, +world: TW.World) -> Plan:
  match verdict:
    case Go{}:
      made(world)
    case Wait{_as, _us}:
      Plan{Still{}, Skip{}, Idle{}, P.Refused{"ez: " ++ TW.target(world) ++ " was never resolved"}}
    case Stop{why}:
      Plan{Still{}, Skip{}, Idle{}, P.Refused{why}}

# `ez tool run`, `install` or `upgrade` over a World
def plan(+world: TW.World) -> Plan:
  plan.v(decide(world), world)

# whether a plan ends in a refusal
def refuses.plan(pl: Plan) -> Bool:
  Plan{_l, _m, _f, outcome} = pl
  match outcome:
    case P.Success{}:
      False{}
    case P.Refused{_why}:
      True{}

# whether a tool command refuses on a World
def refuses(+world: TW.World) -> Bool:
  refuses.plan(plan(world))

# the questions still open, or the plan once there are none
type Step is Data:
  Asking{asks: List<&2, TW.Ask>, ups: List<&2, Up.Ask>}
  Run{plan: Plan}

# the step for where the World stands
def step.v(verdict: Verdict, +world: TW.World) -> Step:
  match verdict:
    case Go{}:
      Run{made(world)}
    case Wait{as, us}:
      Asking{as, us}
    case Stop{why}:
      Run{plan.v(Stop{why}, world)}

# what the interpreter does next on a World
def step(+world: TW.World) -> Step:
  step.v(decide(world), world)

# ---------------------------------------------------------------------------
# `ez tool sync`

# the pins a sync installs, in the order the ledger names them, or why it
# installs none
type Sync is Data:
  Sync{names: List<&2, String>}
  SyncNo{why: String}

# a pin the lock lacks, or has at no commit, stops the scan; any other goes
# on to the rest
def sync.step(bad: Bool, +name: String, rest: Unit -> String) -> String:
  match bad:
    case True{}:
      "ez: tools." ++ name ++ " is not pinned at a commit in ez.lock.toml"
    case False{}:
      rest(Unit{})

# whether the lock pins a tool at a commit
def sync.pinned(+tool: M.Tool) -> Bool:
  Bool.and(Bool.not(String.is_empty(M.tool.name(tool))),
    Git.is_rev(M.source.rev(M.tool.source(tool))))

# every tool the ledger names has to be pinned at a commit in the lock; why
# the first that is not is refused, "" when every one is
def sync.check(ts: List<&2, M.Tool>, +body: String) -> String:
  match ts:
    case []:
      ""
    case +h <> t:
      sync.step(Bool.not(sync.pinned(pin.in(body, M.tool.name(h)))), M.tool.name(h),
        _u => sync.check(t, body))

# the names of the tools a ledger pins
def names.of(ts: List<&2, M.Tool>) -> List<&2, String>:
  match ts:
    case []:
      []
    case h <> t:
      M.tool.name(h) <> names.of(t)

# every name installed, or the refusal the scan found
def sync.why(ok: Bool, +why: String, ts: List<&2, M.Tool>) -> Sync:
  match ok:
    case True{}:
      Sync{names.of(ts)}
    case False{}:
      SyncNo{why}

# a ledger with pins needs a lock that pins each at a commit
def sync.lock(got: Maybe<&2, String>, +ts: List<&2, M.Tool>) -> Sync:
  match got:
    case None{}:
      Bool.pick(Sync, List.is_empty(&2, M.Tool, ts), Sync{[]},
        SyncNo{"ez: ez.lock.toml is not there"})
    case Some{body}:
      +why = sync.check(ts, body)
      sync.why(String.is_empty(why), why, ts)

# a project ledger that does not parse is refused
def sync.read(led: M.Read, got: Maybe<&2, String>) -> Sync:
  match led:
    case M.Bad{why}:
      SyncNo{"ez: error: " ++ why}
    case M.Good{m}:
      sync.lock(got, tools.of(m))

# `ez tool sync` over the project's ledger and lock. With no ledger there is
# no project to sync, and it is refused, as `ez lock` and `ez fetch` refuse
# one.
def sync(ledger: Maybe<&2, String>, lock: Maybe<&2, String>) -> Sync:
  match ledger:
    case None{}:
      SyncNo{"ez: no ez.toml here; ez tool sync installs the tools a project's " ++
        "ledger pins, and ez init makes one"}
    case Some{text}:
      sync.read(M.parse(text), lock)

# how a sync ends once every install it runs has ended: 1 with the reason
# when it refused, and 0 when it did not (EZ-OUT-1). An install that refuses
# ends the sync there, with its own status.
def sync.outcome(synced: Sync) -> P.Outcome:
  match synced:
    case Sync{_ns}:
      P.Success{}
    case SyncNo{why}:
      P.Refused{why}

# whether a sync refuses
def sync.refuses(synced: Sync) -> Bool:
  match synced:
    case Sync{_ns}:
      False{}
    case SyncNo{_why}:
      True{}

# the names a sync installs, none when it refuses
def sync.names(synced: Sync) -> List<&2, String>:
  match synced:
    case Sync{ns}:
      ns
    case SyncNo{_why}:
      []

# ---------------------------------------------------------------------------
# law vocabulary

# whether a checkout is laid
def lays(layout: Lay) -> Bool:
  match layout:
    case Lay{_d, _ws}:
      True{}
    case Still{}:
      False{}

# whether a binary is built
def makes(making: Make) -> Bool:
  match making:
    case Make{_lk, _lb, _fe, _f, _o, _at, _k, _n}:
      True{}
    case Reuse{_n}:
      False{}
    case Skip{}:
      False{}

# whether a link is written
def linked(fin: Finish) -> Bool:
  match fin:
    case Launch{_b, _as}:
      False{}
    case Link{_b, _d, _n, _s}:
      True{}
    case Idle{}:
      False{}

# whether a plan writes anything: a checkout laid, a binary built, a link
def writes(pl: Plan) -> Bool:
  Plan{l, m, f, _o} = pl
  Bool.or(lays(l), Bool.or(makes(m), linked(f)))

# whether a plan builds the binary
def builds(pl: Plan) -> Bool:
  Plan{_l, m, _f, _o} = pl
  makes(m)

# the file a plan builds, "" when it builds none
def built(pl: Plan) -> String:
  Plan{_l, m, _f, _o} = pl
  match m:
    case Make{_lk, _lb, _fe, f, _o, _at, _k, _n}:
      f
    case Reuse{_n}:
      ""
    case Skip{}:
      ""

# whether a plan fetches a lock before it builds
def fetches(pl: Plan) -> Bool:
  Plan{_l, m, _f, _o} = pl
  match m:
    case Make{_lk, _lb, fe, _f, _o, _at, _k, _n}:
      fe
    case Reuse{_n}:
      False{}
    case Skip{}:
      False{}

# the library a plan builds with, "" when it builds nothing
def built.lib(pl: Plan) -> String:
  Plan{_l, m, _f, _o} = pl
  match m:
    case Make{_lk, lb, _fe, _f, _o, _at, _k, _n}:
      lb
    case Reuse{_n}:
      ""
    case Skip{}:
      ""

# whether a plan starts the program
def launches(pl: Plan) -> Bool:
  Plan{_l, _m, f, _o} = pl
  match f:
    case Launch{_b, _as}:
      True{}
    case Link{_b, _d, _n, _s}:
      False{}
    case Idle{}:
      False{}

# the path a plan links, "" when it links none
def link.at(pl: Plan) -> String:
  Plan{_l, _m, f, _o} = pl
  match f:
    case Launch{_b, _as}:
      ""
    case Link{_b, d, n, _s}:
      d ++ "/" ++ n
    case Idle{}:
      ""

# how a command ends: exit 1, having started nothing; exit 0; or with the
# status of this program, started with these words as the last thing
type Exit is Data:
  Refusal{}
  Finished{}
  Exits{bin: String, args: List<&2, String>}

# how a plan that goes on ends
def exit.of(fin: Finish) -> Exit:
  match fin:
    case Launch{b, as}:
      Exits{b, as}
    case Link{_b, _d, _n, _s}:
      Finished{}
    case Idle{}:
      Finished{}

# how a plan ends
def exit(pl: Plan) -> Exit:
  Plan{_l, _m, f, o} = pl
  match o:
    case P.Success{}:
      exit.of(f)
    case P.Refused{_why}:
      Refusal{}

# the status a tool command exits with, given the status the program it
# started exited with (EZ-OUT-1): 1 for a refusal, 0 for a command that
# ends without starting one, and the program's own status for `ez tool run`.
# A command that starts nothing is handed 0 for it.
def code(ended: Exit, program: U32) -> U32:
  match ended:
    case Refusal{}:
      1
    case Finished{}:
      0
    case Exits{_b, _as}:
      program

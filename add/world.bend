# add/world: what `ez add` reads. The arguments it was given; the directory
# it runs in (`here`), which every git question anchors a relative path to;
# HOME, which a `~/` target is expanded against; the ledger's text, None when
# there is no ez.toml; `.gitignore`'s text, "" when there is none; and the
# answers to the questions the planner (add/plan.bend) asked. The questions
# and answers are the upgrade's (lock/up.bend), which the lock's interpreter
# answers: `Tags`, `Head` and `Refs` for what a ref names, and `Clone` for the
# checkout at the rev, with its NAR hash and every file's text. A hub
# package added by its `<name>@<version>` (add/hub.bend) asks the lock's own
# questions instead (lock/world.bend), which the lock's interpreter answers
# too: `Name` for the hash the hub says the name names, and `Pkg` for the
# package's manifest and files, served by the hub. Those answers are `hubs`.
#
# Everything here is a projection: what a World says, read one way. The
# planner is written over these, so each law about the plan is a law about
# them.
import Base
import ../lock/up.bend as Up
import ../lock/world.bend as W
import ../manifest/manifest.bend as M
import ../pkg/path.bend as P
import ../ez/target.bend as Tgt
import ../ez/named.bend as Named

# what `ez add <target> [ref] [entry.bend] [--rename NAME]` was given, each
# "" when it was not
type Args is Data:
  Args{target: String, ref: String, entry: String, rename: String}

# everything `ez add` reads
type World is Data:
  World{args: Args, here: String, home: String, ledger: Maybe<&2, String>,
    ignore: String, replies: List<&2, Up.Reply>, hubs: List<&2, W.Reply>}

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# the ignore file's path, which is fixed
def ignore.file() -> String:
  ".gitignore"

# the arguments
def args(world: World) -> Args:
  World{a, _here, _home, _ledger, _ignore, _replies, _hubs} = world
  a

def args.target(given: Args) -> String:
  Args{t, _ref, _entry, _rename} = given
  t

def args.ref(given: Args) -> String:
  Args{_t, r, _entry, _rename} = given
  r

def args.entry(given: Args) -> String:
  Args{_t, _ref, e, _rename} = given
  e

def args.rename(given: Args) -> String:
  Args{_t, _ref, _entry, r} = given
  r

# the target asked for
def target(world: World) -> String:
  args.target(args(world))

# the ref asked for, "" for none
def ref(world: World) -> String:
  args.ref(args(world))

def entry.arg(world: World) -> String:
  args.entry(args(world))

# the `--rename` asked for, "" for none
def rename(world: World) -> String:
  args.rename(args(world))

# the directory ez runs in, which is the project root
def here(world: World) -> String:
  World{_args, h, _home, _ledger, _ignore, _replies, _hubs} = world
  h

# HOME, which a `~/` target is expanded against
def home(world: World) -> String:
  World{_args, _here, h, _ledger, _ignore, _replies, _hubs} = world
  h

# the ledger's text, None when there is no ez.toml
def ledger(world: World) -> Maybe<&2, String>:
  World{_args, _here, _home, l, _ignore, _replies, _hubs} = world
  l

# `.gitignore`'s text, "" when there is none
def ignore(world: World) -> String:
  World{_args, _here, _home, _ledger, i, _replies, _hubs} = world
  i

# every question answered so far
def replies(world: World) -> List<&2, Up.Reply>:
  World{_args, _here, _home, _ledger, _ignore, rs, _hubs} = world
  rs

# every hub question answered so far
def hubs(world: World) -> List<&2, W.Reply>:
  World{_args, _here, _home, _ledger, _ignore, _replies, hs} = world
  hs

# the ledger as read: what the file says, or, with no file, a read that did
# not parse and says why. A missing ledger is not an empty one to write back.
def read.of(got: Maybe<&2, String>) -> M.Read:
  match got:
    case None{}:
      M.Bad{"no " ++ toml() ++ " here; ez add works on a project's " ++
        "ledger, and ez init makes one"}
    case Some{text}:
      M.parse(text)

# the ledger, read
def read(world: World) -> M.Read:
  read.of(ledger(world))

# the model of a ledger that read; an empty one otherwise, which nothing
# writes, since a ledger that did not read is refused
def manifest.of(led: M.Read) -> M.Manifest:
  match led:
    case M.Bad{_why}:
      M.Manifest{"", "", "", "", [], []}
    case M.Good{m}:
      m

# the dependencies of a ledger that was read
def deps.of(manifest: M.Manifest) -> List<&2, M.Dep>:
  M.Manifest{_n, _e, _b, _h, ds, _ts} = manifest
  ds

# the ledger's dependencies, none when it did not read
def deps(world: World) -> List<&2, M.Dep>:
  deps.of(manifest.of(read(world)))

# where the target names
def place(world: World) -> Tgt.Place:
  Tgt.classify(target(world))

# the source a place records: a URL as it is, a path as it was given with a
# leading `~/` expanded against HOME, and nothing for a target that names
# nothing
def url.of(place: Tgt.Place, +home: String) -> String:
  match place:
    case Tgt.Bad{_why}:
      ""
    case Tgt.Local{path}:
      Tgt.expand(home, path)
    case Tgt.Remote{url, _slug}:
      url

# the source the ledger records (EZ-LED-8)
def url(+world: World) -> String:
  url.of(place(world), home(world))

# the source as git is to read it: a relative path taken from where ez runs,
# which is the project root. Every question the planner asks carries this.
def from(+world: World) -> String:
  P.anchor(here(world), url(world))

# the name the source gives itself: a repository's, or the directory's the
# path resolves to
def fresh(+world: World) -> String:
  Named.called(place(world), from(world))

# what the target names: a hub package by its `<name>@<version>`, or a place
def aim(world: World) -> Tgt.Aim:
  Tgt.aim(target(world))

# whether the target is a hub package's `<name>@<version>`
def named(world: World) -> Bool:
  Tgt.aim.named(aim(world))

# the hub the ledger names, which a name and its package are asked of
def hub(world: World) -> String:
  M.hub_of(read(world))

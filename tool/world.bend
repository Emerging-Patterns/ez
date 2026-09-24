# tool/world: what `ez tool run`, `install` and `upgrade` read. The act and
# the target they were given; the directory they run in (`here`), which a
# relative cache root is taken from; the variables that place the cache and
# the link (`EZ_TOOL_BIN`, `XDG_BIN_HOME`, `XDG_CACHE_HOME`, `HOME`, `PATH`);
# the bend on the PATH, as its banner's first line; the file `--entry` names,
# "" when it names none; the project's ledger and lock, None when there is
# none; and the answers to the questions the planner (tool/plan.bend)
# asked. `ez tool sync` reads only the ledger and the lock.
#
# A question is a file's text, whether a binary is there, what git says of a
# local path, or one of the upgrade's (lock/up.bend): `Head` for the commit a
# remote's HEAD names, and `Clone` for the checkout at a rev with every
# file's text. The upgrade's are answered by the lock's interpreter and kept
# apart, in `ups`, so its lookups serve here as they are.
#
# Everything else here is a projection: what a World says, read one way.
import Base
import ../lock/up.bend as Up
import ../manifest/manifest.bend as M
import ../pkg/path.bend as P

# what the command does with the binary once it is current: `Run` starts it
# with these words, `Install` and `Upgrade` link it onto PATH
type Act is Data:
  Run{args: List<&2, String>}
  Install{}
  Upgrade{}

# the variables the command reads, each "" when it is unset
type Env is Data:
  Env{tool_bin: String, xdg_bin: String, xdg_cache: String, home: String, path: String}

# a question the planner asks that is not git's about a remote
type Ask is Data:
  Read{path: String}      # a file's text, None when there is none
  Exec{path: String}      # whether a file is there and executable
  Locate{path: String}    # what git says of a local path

# the answer to one: a file's text, whether a binary is there, or what git
# said of a path: its real path, the top of the checkout holding it, the
# commit HEAD names, and whether `git status` answered and what it printed.
# A path that has no real path, or a question IO could not answer, is a miss.
type Answer is Data:
  Text{got: Maybe<&2, String>}
  Is{yes: Bool}
  Located{abs: String, top: String, head: String, ok: Bool, status: String}
  Miss{why: String}

# one question, answered
type Reply is Data:
  Reply{ask: Ask, answer: Answer}

# everything `ez tool run`, `install` and `upgrade` read
type World is Data:
  World{act: Act, target: String, want: String, here: String, env: Env, bend: String,
    ledger: Maybe<&2, String>, lock: Maybe<&2, String>, replies: List<&2, Reply>,
    ups: List<&2, Up.Reply>}

# the act
def act(world: World) -> Act:
  World{a, _t, _want, _here, _env, _bend, _ledger, _lock, _rs, _ups} = world
  a

# the target asked for
def target(world: World) -> String:
  World{_a, t, _want, _here, _env, _bend, _ledger, _lock, _rs, _ups} = world
  t

# the file `--entry` names, "" when it names none
def want(world: World) -> String:
  World{_a, _t, w, _here, _env, _bend, _ledger, _lock, _rs, _ups} = world
  w

# the directory ez runs in
def here(world: World) -> String:
  World{_a, _t, _want, h, _env, _bend, _ledger, _lock, _rs, _ups} = world
  h

# the variables
def env(world: World) -> Env:
  World{_a, _t, _want, _here, e, _bend, _ledger, _lock, _rs, _ups} = world
  e

# the bend on the PATH, "" when it did not answer
def bend(world: World) -> String:
  World{_a, _t, _want, _here, _env, b, _ledger, _lock, _rs, _ups} = world
  b

# the project's ez.toml, None when there is none
def ledger(world: World) -> Maybe<&2, String>:
  World{_a, _t, _want, _here, _env, _bend, l, _lock, _rs, _ups} = world
  l

# the project's ez.lock.toml, None when there is none
def lock(world: World) -> Maybe<&2, String>:
  World{_a, _t, _want, _here, _env, _bend, _ledger, l, _rs, _ups} = world
  l

# every question of ours answered so far
def replies(world: World) -> List<&2, Reply>:
  World{_a, _t, _want, _here, _env, _bend, _ledger, _lock, rs, _ups} = world
  rs

# every one of the upgrade's questions answered so far
def ups(world: World) -> List<&2, Up.Reply>:
  World{_a, _t, _want, _here, _env, _bend, _ledger, _lock, _rs, us} = world
  us

def env.tool_bin(vars: Env) -> String:
  Env{b, _x, _c, _h, _p} = vars
  b

def env.xdg_bin(vars: Env) -> String:
  Env{_b, x, _c, _h, _p} = vars
  x

def env.xdg_cache(vars: Env) -> String:
  Env{_b, _x, c, _h, _p} = vars
  c

def env.home(vars: Env) -> String:
  Env{_b, _x, _c, h, _p} = vars
  h

def env.path(vars: Env) -> String:
  Env{_b, _x, _c, _h, p} = vars
  p

# HOME
def home(world: World) -> String:
  env.home(env(world))

# ---------------------------------------------------------------------------
# where things go

# `~/.local/bin`, when there is a HOME
def bin.home(+home: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(home), None{}, Some{home ++ "/.local/bin"})

# `$XDG_BIN_HOME` when it is set, otherwise the one above
def bin.xdg(+xdg: String, +home: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(xdg), bin.home(home), Some{xdg})

# where an installed command is linked: `$EZ_TOOL_BIN` when it is set,
# otherwise `$XDG_BIN_HOME`, otherwise `$HOME/.local/bin`, an empty value
# counting as unset; None when all three are empty (EZ-TOOL-1)
def bin.dir(+ez: String, +xdg: String, +home: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(ez), bin.xdg(xdg, home), Some{ez})

# the link directory of a World's variables
def bin.of(vars: Env) -> Maybe<&2, String>:
  Env{+b, +x, _c, +h, _p} = vars
  bin.dir(b, x, h)

# the cache root: `$XDG_CACHE_HOME/ez/tool`, otherwise `$HOME/.cache/ez/tool`,
# taken from where ez runs when it is relative, so every path the plan names
# is absolute; None when neither variable is set
def cache.home(+here: String, +home: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(home), None{},
    Some{P.anchor(here, home) ++ "/.cache/ez/tool"})

def cache.dir(+here: String, +xdg: String, +home: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.is_empty(xdg), cache.home(here, home),
    Some{P.anchor(here, xdg) ++ "/ez/tool"})

# the cache root of a World
def cache.of(world: World) -> Maybe<&2, String>:
  World{_a, _t, _want, +here, vars, _bend, _ledger, _lock, _rs, _ups} = world
  Env{_b, _x, +c, +h, _p} = vars
  cache.dir(here, c, h)

# a Maybe's text, "" for none
def text.or(got: Maybe<&2, String>) -> String:
  match got:
    case None{}:
      ""
    case Some{t}:
      t

# ---------------------------------------------------------------------------
# the project

# the project's ledger as read. A project with no ez.toml pins nothing, so
# every target is a free one; one that does not parse is its own refusal.
def project.of(got: Maybe<&2, String>) -> M.Read:
  match got:
    case None{}:
      M.Good{M.Manifest{"", "", "", "", "", "", [], []}}
    case Some{text}:
      M.parse(text)

# the project's ledger as read
def project(world: World) -> M.Read:
  project.of(ledger(world))

# ---------------------------------------------------------------------------
# answers

# the key a question is looked up by
def key(ask: Ask) -> String:
  match ask:
    case Read{path}:
      "read\n" ++ path
    case Exec{path}:
      "exec\n" ++ path
    case Locate{path}:
      "locate\n" ++ path

# an answer looked up, or none yet
type Heard is Data:
  Heard{answer: Answer}
  Open{}

# this answer when it is the question's, otherwise the rest's
def look.step(hit: Bool, answer: Answer, rest: Unit -> Heard) -> Heard:
  match hit:
    case True{}:
      Heard{answer}
    case False{}:
      rest(Unit{})

# the first answer given to a question
def look(rs: List<&2, Reply>, +want: String) -> Heard:
  match rs:
    case []:
      Open{}
    case Reply{ask, answer} <> t:
      look.step(String.eq(key(ask), want), answer, _u => look(t, want))

# the answer to a question, or none yet
def heard(+world: World, ask: Ask) -> Heard:
  look(replies(world), key(ask))

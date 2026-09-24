# fetch/world: what `ez fetch` reads. The directory the project is in
# (`here`), which a relative path in the lock is anchored to; whether there is
# an ez.toml, since fetch fills BEND_LIB for a project and nothing else; the
# lock's text, None when there is no ez.lock.toml; and the answers to the
# questions the planner (fetch/plan.bend) asked. There is no field for
# BEND_LIB's path, the environment or the clock, because the planner reads
# none of them.
#
# A question is about one package of the lock, by its hash: the tree already
# under BEND_LIB (`Laid`), or the package fetched from where the lock says it
# comes from. A git package is the upgrade's own `Clone` question
# (lock/up.bend), a shallow checkout at the pinned rev with every file's
# text; a hub package is the lock's own question (lock/world.bend), the
# hub's manifest and every file it names. `Laid` and a hub package are
# answered the way the lock answers its questions, with a manifest and the
# texts of the files it names, and a clone the way the upgrade answers
# `Clone`.
#
# A name the lock records is asked about too: the file bend reads its hash
# from, `$BEND_LIB/names/<nv>` (`Named`), as it is, or that there is none.
import Base
import 0x04b9afdd6d6a56039c5ce6dfb1e55294/toml.bend as T
import ../lock/lock.bend as L
import ../lock/world.bend as W
import ../lock/up.bend as Up

# a question about one package of the lock, or one name it records
type Ask is Data:
  Laid{hash: String}               # the tree under BEND_LIB/<hash>, as its manifest names it
  Git{hash: String, ask: Up.Ask}   # a checkout at the pinned rev (`Up.Clone`)
  Hub{ask: W.Ask}                  # the hub's manifest and every file it names (`W.Pkg`)
  Named{nv: String}                # the file BEND_LIB/names/<nv>, as it is

# the answer to one question: a manifest and the texts of the files it
# names, what a clone answered, or a names file's text, None when there is
# none
type Answer is Data:
  Read{answer: W.Answer}           # Laid, Hub
  Said{answer: Up.Answer}          # Git
  Held{got: Maybe<&2, String>}     # Named

# one question, answered
type Reply is Data:
  Reply{ask: Ask, answer: Answer}

# everything `ez fetch` reads
type World is Data:
  World{here: String, ledger: Bool, lock: Maybe<&2, String>, replies: List<&2, Reply>}

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# the lock's path, which is fixed
def lockfile() -> String:
  "ez.lock.toml"

# the directory the project is in, which every relative path in the lock is
# read against
def here(world: World) -> String:
  World{h, _ledger, _lock, _replies} = world
  h

# whether there is an ez.toml
def ledger(world: World) -> Bool:
  World{_here, l, _lock, _replies} = world
  l

# the lock's text, None when there is no ez.lock.toml
def lock(world: World) -> Maybe<&2, String>:
  World{_here, _ledger, l, _replies} = world
  l

# every question answered so far
def replies(world: World) -> List<&2, Reply>:
  World{_here, _ledger, _lock, rs} = world
  rs

# a lock's text, as tables; none when there is no lock
def sects.of(got: Maybe<&2, String>) -> List<&2, T.Sect>:
  match got:
    case None{}:
      []
    case Some{text}:
      T.sects(T.parse(text))

# the lock, as tables
def sects(world: World) -> List<&2, T.Sect>:
  sects.of(lock(world))

# a hub question as a key
def hub.key(ask: W.Ask) -> String:
  match ask:
    case W.Pkg{hash, _src, hub}:
      "hub\n" ++ hash ++ "\n" ++ hub
    case W.Name{nv, hub}:
      "hubname\n" ++ nv ++ "\n" ++ hub
    case W.Lock{}:
      "hublock"

# a question as a key. A lock's value never holds a newline, so the fields
# are kept apart by one.
def key(ask: Ask) -> String:
  match ask:
    case Laid{hash}:
      "laid\n" ++ hash
    case Git{hash, q}:
      "git\n" ++ hash ++ "\n" ++ Up.key(q)
    case Hub{q}:
      hub.key(q)
    case Named{nv}:
      "named\n" ++ nv

# an answer looked up, or none yet
type Heard is Data:
  Heard{answer: Answer}
  Open{}

# this answer when it is the question's, otherwise the rest's. The rest
# arrives as a thunk, so the first hit ends the scan.
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
def heard(rs: List<&2, Reply>, ask: Ask) -> Heard:
  look(rs, key(ask))

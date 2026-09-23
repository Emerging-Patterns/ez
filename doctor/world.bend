# doctor/world: what `ez doctor` reads. The C compiler `$CC` names ("" when
# it is unset) and `$BEND_LIB` ("" when it is unset), which the planner
# (doctor/plan.bend) turns into the compiler and the library it reports on;
# the ledger's text and the lock's text, None when there is no file; and the
# answers to the questions the planner asked. There is no field for the
# clock or the rest of the environment, because the planner reads neither.
#
# A question is a program asked for its version, the names of the packages
# under BEND_LIB, the project's sources, or a package's tree under BEND_LIB.
# The sources are every `.bend` file git tracks, with its text, which is the
# lock's own listing (`W.Listing`), read the way `ez lock` reads it. So doctor
# judges the import lines `ez lock` judges. A tree is asked about with the
# lock's own question (`W.Ask`) and answered only from BEND_LIB: the manifest
# there and the text of each file it names, or that there is none. Doctor
# never asks the network, so this is all it can know of a package.
import Base
import ../lock/world.bend as W
import ../manifest/manifest.bend as M

# a question the planner asks
type Ask is Data:
  Probe{name: String}   # the program asked for its version
  Lib{dir: String}      # the names under the library directory, as `ls` prints them
  Sources{}             # every `.bend` file git tracks, with its text
  Tree{ask: W.Ask}      # the lock's question about a package, put to BEND_LIB

# the answer to one: what a program printed, and whether it ran; or the
# sources as the lock lists them; or a package's tree as BEND_LIB holds it,
# or that BEND_LIB holds none
type Answer is Data:
  Printed{ok: Bool, text: String}                  # Probe, Lib
  Listed{listing: W.Listing}                       # Sources
  Laid{manifest: String, srcs: List<&2, String>}   # Tree, there
  Away{}                                           # Tree, not there

# one question, answered
type Reply is Data:
  Reply{ask: Ask, answer: Answer}

# everything `ez doctor` reads
type World is Data:
  World{cc: String, lib: String, ledger: Maybe<&2, String>, lock: Maybe<&2, String>,
    replies: List<&2, Reply>}

# the ledger's path, which is fixed
def toml() -> String:
  "ez.toml"

# the lock's path, which is fixed
def lockfile() -> String:
  "ez.lock.toml"

# what `$CC` holds, "" when it is unset
def cc(world: World) -> String:
  World{c, _lib, _ledger, _lock, _replies} = world
  c

# what `$BEND_LIB` holds, "" when it is unset
def lib(world: World) -> String:
  World{_cc, l, _ledger, _lock, _replies} = world
  l

# the ledger's text, None when there is no ez.toml
def ledger(world: World) -> Maybe<&2, String>:
  World{_cc, _lib, l, _lock, _replies} = world
  l

# the lock's text, None when there is no ez.lock.toml
def lock(world: World) -> Maybe<&2, String>:
  World{_cc, _lib, _ledger, l, _replies} = world
  l

# every question answered so far
def replies(world: World) -> List<&2, Reply>:
  World{_cc, _lib, _ledger, _lock, rs} = world
  rs

# the ledger as read: what the file says, or, with no file, a read that did
# not parse and says why, as every command that reads a ledger says it
def read.of(got: Maybe<&2, String>) -> M.Read:
  match got:
    case None{}:
      M.Bad{"none here; ez init makes one"}
    case Some{text}:
      M.parse(text)

# the ledger, read
def read(world: World) -> M.Read:
  read.of(ledger(world))

# a question as a key. A program's name and a directory hold no newline, so
# the fields are kept apart by one.
def key(ask: Ask) -> String:
  match ask:
    case Probe{name}:
      "probe\n" ++ name
    case Lib{dir}:
      "lib\n" ++ dir
    case Sources{}:
      "sources"
    case Tree{ask}:
      "tree\n" ++ W.ask.hash(ask)

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

# the answer the sources question has had on a World, or none yet
def sources(world: World) -> Heard:
  heard(replies(world), Sources{})
